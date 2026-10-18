#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Berga TV - player pessoal de TV (M3U / Xtream Codes) com guia de programacao.

Como usar:
    python berga_tv.py           -> abre no navegador deste computador
    python berga_tv.py --lan     -> libera para TV/celular na mesma rede Wi-Fi
    python berga_tv.py --port 9000 --no-browser

Nao precisa instalar nada alem do Python 3.8+.
O servidor local faz a ponte com o provedor (evita bloqueios de CORS do navegador,
ajusta playlists HLS e processa o guia EPG, que costuma ser enorme).
"""
import gzip
import hashlib
import io
import json
import os
import re
import socket
import ssl
import sys
import threading
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

VERSION = "1.2.0"
DEFAULT_UA = "VLC/3.0.20 LibVLC/3.0.20"
CACHE_DIR = os.path.join(os.path.expanduser("~"), ".berga_iptv")

_ctx = ssl.create_default_context()
_ctx.check_hostname = False
_ctx.verify_mode = ssl.CERT_NONE
OPENER = urllib.request.build_opener(urllib.request.HTTPSHandler(context=_ctx))


def upstream(url, ua=None, rng=None, timeout=30):
    if not re.match(r"^https?://", url or "", re.I):
        raise ValueError("URL invalida: %s" % url)
    headers = {"User-Agent": ua or DEFAULT_UA, "Accept": "*/*", "Connection": "close"}
    if rng:
        headers["Range"] = rng
    req = urllib.request.Request(url, headers=headers)
    try:
        return OPENER.open(req, timeout=timeout)
    except urllib.error.HTTPError as e:
        return e


def proxify(u, ua):
    q = "/p?u=" + urllib.parse.quote(u, safe="")
    if ua:
        q += "&ua=" + urllib.parse.quote(ua, safe="")
    return q


def rewrite_m3u8(text, base, ua):
    out = []
    for line in text.splitlines():
        s = line.strip()
        if not s:
            continue
        if s.startswith("#"):
            if 'URI="' in s:
                s = re.sub(r'URI="([^"]+)"',
                           lambda m: 'URI="%s"' % proxify(urllib.parse.urljoin(base, m.group(1)), ua), s)
            out.append(s)
        else:
            out.append(proxify(urllib.parse.urljoin(base, s), ua))
    return "\n".join(out) + "\n"


# ---------------------------------------------------------------- EPG (XMLTV)
def norm(s):
    s = unicodedata.normalize("NFKD", str(s or "")).encode("ascii", "ignore").decode().lower()
    s = re.sub(r"\b(fhd|uhd|hd|sd|4k|h265|hevc|alt)\b", " ", s)
    return re.sub(r"[^a-z0-9]", "", s)


def xmltv_time(s):
    s = (s or "").strip()
    dt = datetime.strptime(s[:14], "%Y%m%d%H%M%S").replace(tzinfo=timezone.utc)
    tz = s[14:].strip()
    if tz and tz[0] in "+-" and len(tz) >= 5:
        off = timedelta(hours=int(tz[1:3]), minutes=int(tz[3:5]))
        dt = dt - off if tz[0] == "+" else dt + off
    return int(dt.timestamp())


class AmpFix(object):
    """Corrige '&' soltos (comum em guias EPG mal formados) enquanto le o arquivo."""
    RX = re.compile(rb"&(?!#?[A-Za-z0-9]{1,10};)")

    def __init__(self, f):
        self.f, self.buf, self.eof = f, b"", False

    def read(self, n=65536):
        while not self.eof and len(self.buf) < n:
            c = self.f.read(65536)
            if not c:
                self.eof = True
            self.buf += c
        if self.eof:
            out, self.buf = self.buf, b""
        else:
            cut = len(self.buf)
            amp = self.buf.rfind(b"&", max(0, cut - 12))
            if amp != -1:
                cut = amp
            out, self.buf = self.buf[:cut], self.buf[cut:]
            if not out:
                out, self.buf = self.buf, b""
        return self.RX.sub(b"&amp;", out)


def build_epg(url, ua):
    r = upstream(url, ua, timeout=240)
    if r.getcode() >= 400:
        raise RuntimeError("o provedor respondeu HTTP %d no guia" % r.getcode())
    head = r.peek(2)[:2] if hasattr(r, "peek") else b""
    src = gzip.GzipFile(fileobj=r) if head == b"\x1f\x8b" else r
    now = time.time()
    lo, hi = now - 2 * 3600, now + 20 * 3600
    names, progs = {}, {}
    try:
        for _ev, el in ET.iterparse(AmpFix(src), events=("end",)):
            tag = el.tag
            if tag == "channel":
                cid = el.get("id") or ""
                if cid:
                    names.setdefault(norm(cid), cid)
                    for d in el.findall("display-name"):
                        if d.text:
                            names.setdefault(norm(d.text), cid)
                el.clear()
            elif tag == "programme":
                try:
                    st = xmltv_time(el.get("start"))
                    en = xmltv_time(el.get("stop")) if el.get("stop") else st + 3600
                except Exception:
                    el.clear()
                    continue
                if en >= lo and st <= hi:
                    t = (el.findtext("title") or "").strip()
                    d = (el.findtext("desc") or "").strip()
                    if len(d) > 180:
                        d = d[:177].rstrip() + "..."
                    progs.setdefault(el.get("channel") or "", []).append([st, en, t, d])
                el.clear()
    except ET.ParseError as e:
        if not progs:
            raise RuntimeError("guia EPG invalido (%s)" % e)
    finally:
        try:
            r.close()
        except Exception:
            pass
    names.pop("", None)
    for v in progs.values():
        v.sort(key=lambda p: p[0])
    return json.dumps({"gerado": int(now), "progs": progs, "names": names},
                      ensure_ascii=False, separators=(",", ":")).encode("utf-8")


_epg_mem, _epg_locks, _glock = {}, {}, threading.Lock()


def epg_json(url, ua, force=False):
    key = hashlib.sha1(url.encode("utf-8")).hexdigest()[:16]
    with _glock:
        lock = _epg_locks.setdefault(key, threading.Lock())
    with lock:
        m = _epg_mem.get(key)
        if m and not force and time.time() - m[0] < 3 * 3600:
            return m[1]
        path = os.path.join(CACHE_DIR, "epg_%s.json" % key)
        if not force and os.path.exists(path) and time.time() - os.path.getmtime(path) < 4 * 3600:
            with open(path, "rb") as f:
                data = f.read()
            _epg_mem[key] = (os.path.getmtime(path), data)
            return data
        data = build_epg(url, ua)
        _epg_mem[key] = (time.time(), data)
        try:
            os.makedirs(CACHE_DIR, exist_ok=True)
            with open(path, "wb") as f:
                f.write(data)
        except OSError:
            pass
        return data


# ---------------------------------------------------------------- downloads
def default_dl_dir():
    base = os.path.join(os.path.expanduser("~"), "Downloads")
    if not os.path.isdir(base):
        base = os.path.expanduser("~")
    return os.path.join(base, "Berga TV")


def safe_name(s, maxlen=120):
    s = re.sub(r'[<>:"/\\|?*\x00-\x1f]', " ", str(s or "")).strip().rstrip(". ")
    s = re.sub(r"\s+", " ", s)
    s = s[:maxlen].rstrip(". ")
    if s.upper().split(".")[0] in ("CON", "PRN", "AUX", "NUL", "COM1", "LPT1"):
        s = "_" + s
    return s or "sem nome"


class Downloads(object):
    """Fila de downloads com pausa/retomada. Estado salvo em ~/.berga_iptv/downloads.json"""

    def __init__(self):
        self.lock = threading.RLock()
        self.items = []
        self.cfg = {"dir": default_dl_dir(), "max": 1}
        self.state_path = os.path.join(CACHE_DIR, "downloads.json")
        self.workers = {}
        self._dirty = 0
        try:
            with open(self.state_path, "r", encoding="utf-8") as f:
                st = json.load(f)
            self.items = st.get("items", [])
            self.cfg.update(st.get("cfg", {}))
        except (OSError, ValueError):
            pass
        old_default = os.path.join(os.path.dirname(default_dl_dir()), "Berga IPTV")
        if self.cfg.get("dir") == old_default and not os.path.isdir(old_default):
            self.cfg["dir"] = default_dl_dir()
        now = time.time()
        for it in self.items:
            it.pop("speed", None)
            if it.get("kind") == "rec":
                if it["status"] in ("gravando", "agendado"):
                    if now < it.get("end", 0):
                        it["status"] = "agendado"
                    elif os.path.exists(it["path"] + ".part"):
                        self._finish_rec(it, "Gravação interrompida (o app foi fechado)")
                    else:
                        it["status"], it["msg"] = "erro", "O computador estava desligado no horário"
                continue
            if it["status"] in ("baixando", "fila"):
                it["status"] = "pausado"
                it["msg"] = "Interrompido ao fechar o app"
        self.save()
        threading.Thread(target=self._rec_loop, daemon=True).start()

    def save(self):
        with self.lock:
            data = json.dumps({"cfg": self.cfg, "items": self.items}, ensure_ascii=False)
        try:
            os.makedirs(CACHE_DIR, exist_ok=True)
            tmp = self.state_path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                f.write(data)
            os.replace(tmp, self.state_path)
        except OSError:
            pass

    def find(self, did):
        for it in self.items:
            if it["id"] == did:
                return it
        return None

    def snapshot(self):
        with self.lock:
            out = []
            for it in self.items:
                d = dict(it)
                d.pop("url", None)
                d.pop("ua", None)
                d["exists"] = it["status"] == "concluido" and os.path.exists(it["path"])
                out.append(d)
            return {"dir": self.cfg["dir"], "max": self.cfg["max"], "items": out}

    def add(self, entries, ua):
        added = 0
        with self.lock:
            for e in entries:
                url = e.get("url") or ""
                if not re.match(r"^https?://", url, re.I):
                    continue
                rec = e.get("kind") == "rec"
                if rec:
                    if any(x.get("k") == e.get("k") and x["status"] != "erro" for x in self.items):
                        continue
                    try:
                        start, end = int(e.get("start")), int(e.get("end"))
                    except (TypeError, ValueError):
                        continue
                    if end <= time.time():
                        continue
                elif any(x["url"] == url and x["status"] != "erro" for x in self.items):
                    continue
                ext = os.path.splitext(urllib.parse.urlsplit(url).path)[1].lower()
                if rec:
                    ext = ".ts"
                elif not re.match(r"^\.[a-z0-9]{2,4}$", ext):
                    ext = ".mp4"
                sub = [safe_name(x, 80) for x in (e.get("folder") or []) if x]
                d = os.path.join(self.cfg["dir"], *sub)
                path = os.path.join(d, safe_name(e.get("filename") or e.get("name")) + ext)
                n = 2
                base = path[: -len(ext)]
                while os.path.exists(path) or any(x["path"] == path for x in self.items):
                    path = "%s (%d)%s" % (base, n, ext)
                    n += 1
                self.items.append({
                    "id": hashlib.sha1((url + str(time.time())).encode()).hexdigest()[:12],
                    "k": e.get("k") or "", "name": e.get("name") or "", "logo": e.get("logo") or "",
                    "kind": e.get("kind") or "movie", "url": url, "ua": ua or "", "path": path, "ext": ext,
                    "status": "agendado" if rec else "fila", "done": 0, "total": 0, "msg": "", "added": int(time.time()),
                })
                if rec:
                    self.items[-1].update({"start": start, "end": end, "channel": e.get("channel") or "", "prog": e.get("prog") or ""})
                added += 1
        self.save()
        self.pump()
        return added

    # ------------------------------------------------------------ gravações
    def _rec_loop(self):
        while True:
            now = time.time()
            with self.lock:
                for it in self.items:
                    if it.get("kind") != "rec" or it["status"] != "agendado":
                        continue
                    if now >= it["end"]:
                        it["status"], it["msg"] = "erro", "O horário passou antes de começar"
                    elif now >= it["start"] - 60 and it["id"] not in self.workers:
                        it["status"], it["msg"] = "gravando", ""
                        t = threading.Thread(target=self._record, args=(it,), daemon=True)
                        self.workers[it["id"]] = t
                        t.start()
            time.sleep(5)

    def _finish_rec(self, it, msg=""):
        part = it["path"] + ".part"
        if it.get("fmp4") and it["path"].endswith(".ts"):
            it["path"], it["ext"] = it["path"][:-3] + ".mp4", ".mp4"
        if os.path.exists(part) and os.path.getsize(part) > 0:
            try:
                os.replace(part, it["path"])
            except OSError:
                pass
            it["status"], it["msg"] = "concluido", msg
            it["total"] = it["done"] = os.path.getsize(it["path"])
            it["finished"] = int(time.time())
        else:
            it["status"], it["msg"] = "erro", msg or "Nada foi gravado (canal fora do ar?)"

    def _record(self, it):
        part = it["path"] + ".part"
        stop_at = it["end"] + 120
        fails = 0
        seen = []
        try:
            os.makedirs(os.path.dirname(part), exist_ok=True)
            with open(part, "ab") as f:
                while it["status"] == "gravando" and time.time() < stop_at:
                    try:
                        r = upstream(it["url"], it["ua"], timeout=30)
                        if r.getcode() >= 400:
                            raise RuntimeError("o provedor respondeu HTTP %d" % r.getcode())
                        first = r.read(2048)
                        if first.lstrip(b"\xef\xbb\xbf \r\n\t").startswith(b"#EXTM3U"):
                            self._record_hls(it, r.geturl(), (first + r.read()).decode("utf-8", "replace"), f, stop_at, seen)
                        else:
                            f.write(first)
                            self._add_done(it, len(first))
                            reader = getattr(r, "read1", None) or r.read
                            while it["status"] == "gravando" and time.time() < stop_at:
                                chunk = reader(65536)
                                if not chunk:
                                    break
                                f.write(chunk)
                                self._add_done(it, len(chunk))
                                if fails:
                                    fails, it["msg"] = 0, ""
                        r.close()
                    except Exception as e:
                        fails += 1
                        it["msg"] = "Reconectando… (%s)" % (str(e)[:80] or e.__class__.__name__)
                    if it["status"] == "gravando" and time.time() < stop_at:
                        time.sleep(min(15, 2 + fails * 2))
        except Exception as e:
            it["msg"] = str(e)
        finally:
            with self.lock:
                self.workers.pop(it["id"], None)
                if it["status"] in ("gravando",):
                    self._finish_rec(it)
                elif it["status"] == "parado":
                    self._finish_rec(it, "Gravação parada antes do fim")
            self.save()

    def _add_done(self, it, n):
        with self.lock:
            it["done"] += n

    def _record_hls(self, it, url, text, f, stop_at, seen):
        """Grava uma transmissão HLS juntando os segmentos .ts em um único arquivo."""
        while it["status"] == "gravando" and time.time() < stop_at:
            lines = [l.strip() for l in text.splitlines() if l.strip()]
            if any(l.startswith("#EXT-X-STREAM-INF") for l in lines):
                variants = [l for l in lines if not l.startswith("#")]
                url = urllib.parse.urljoin(url, variants[-1])
                r = upstream(url, it["ua"], timeout=30)
                text = r.read().decode("utf-8", "replace")
                r.close()
                continue
            target = 6
            for l in lines:
                if l.startswith("#EXT-X-TARGETDURATION:"):
                    try:
                        target = max(1, int(float(l.split(":", 1)[1])))
                    except ValueError:
                        pass
            for l in lines:
                m = re.match(r'#EXT-X-MAP:.*URI="([^"]+)"', l)
                if m and not it.get("fmp4"):
                    r = upstream(urllib.parse.urljoin(url, m.group(1)), it["ua"], timeout=30)
                    data = r.read()
                    r.close()
                    f.write(data)
                    self._add_done(it, len(data))
                    it["fmp4"] = True
            for l in lines:
                if l.startswith("#"):
                    continue
                seg = urllib.parse.urljoin(url, l)
                if seg in seen:
                    continue
                seen.append(seg)
                del seen[:-200]
                r = upstream(seg, it["ua"], timeout=30)
                data = r.read()
                r.close()
                f.write(data)
                self._add_done(it, len(data))
                it["msg"] = ""
            if "#EXT-X-ENDLIST" in text:
                return
            time.sleep(max(1, target / 2.0))
            r = upstream(url, it["ua"], timeout=30)
            text = r.read().decode("utf-8", "replace")
            r.close()

    def pump(self):
        with self.lock:
            running = sum(1 for x in self.items if x["status"] == "baixando")
            for it in self.items:
                if running >= max(1, int(self.cfg.get("max") or 1)):
                    break
                if it["status"] == "fila" and it["id"] not in self.workers:
                    it["status"] = "baixando"
                    it["msg"] = ""
                    running += 1
                    t = threading.Thread(target=self.run, args=(it,), daemon=True)
                    self.workers[it["id"]] = t
                    t.start()

    def act(self, did, action):
        with self.lock:
            it = self.find(did)
            if not it:
                return False
            if action == "stop" and it.get("kind") == "rec":
                if it["status"] == "gravando":
                    it["status"] = "parado"
                elif it["status"] == "agendado":
                    self.items.remove(it)
                self.save()
                return True
            if action == "pause" and it["status"] in ("baixando", "fila"):
                it["status"] = "pausado"
                it["msg"] = ""
            elif action == "resume" and it["status"] in ("pausado", "erro"):
                it["status"] = "fila"
                it["msg"] = ""
            elif action in ("cancel", "delete", "remove"):
                was = it["status"]
                it["status"] = "removido"
                self.items.remove(it)
                if action in ("cancel", "delete"):
                    for pth in (it["path"] + ".part", it["path"] if action == "delete" or was != "concluido" else None):
                        if pth:
                            threading.Thread(target=self._rm, args=(pth,), daemon=True).start()
        self.save()
        self.pump()
        return True

    @staticmethod
    def _rm(pth):
        for _ in range(20):
            try:
                if os.path.exists(pth):
                    os.remove(pth)
                return
            except OSError:
                time.sleep(0.5)

    def set_cfg(self, dirpath=None, mx=None):
        with self.lock:
            if dirpath:
                dirpath = os.path.abspath(os.path.expanduser(dirpath))
                os.makedirs(dirpath, exist_ok=True)
                self.cfg["dir"] = dirpath
            if mx:
                self.cfg["max"] = max(1, min(4, int(mx)))
        self.save()
        self.pump()

    def run(self, it):
        part = it["path"] + ".part"
        last_save = time.time()
        try:
            os.makedirs(os.path.dirname(part), exist_ok=True)
            have = os.path.getsize(part) if os.path.exists(part) else 0
            r = upstream(it["url"], it["ua"], "bytes=%d-" % have if have else None, timeout=40)
            code = r.getcode()
            if code == 416 and have:
                r.close()
                os.replace(part, it["path"])
                with self.lock:
                    it["status"], it["done"] = "concluido", have
                    it["total"] = it["total"] or have
                return
            if code >= 400:
                raise RuntimeError("o provedor respondeu HTTP %d" % code)
            if code != 206:
                have = 0
            cl = int(r.headers.get("Content-Length") or 0)
            with self.lock:
                it["total"] = have + cl if cl else 0
                it["done"] = have
            win_t, win_b = time.time(), have
            reader = getattr(r, "read1", None) or r.read
            with open(part, "ab" if have else "wb") as f:
                while True:
                    if it["status"] != "baixando":
                        break
                    chunk = reader(256 * 1024)
                    if not chunk:
                        break
                    f.write(chunk)
                    with self.lock:
                        it["done"] += len(chunk)
                        now = time.time()
                        if now - win_t >= 1:
                            it["speed"] = int((it["done"] - win_b) / (now - win_t))
                            win_t, win_b = now, it["done"]
                    if time.time() - last_save > 10:
                        last_save = time.time()
                        self.save()
            r.close()
            with self.lock:
                it.pop("speed", None)
                if it["status"] == "baixando":
                    if it["total"] and it["done"] < it["total"]:
                        it["status"], it["msg"] = "pausado", "Conexão interrompida - clique em Retomar"
                    else:
                        os.replace(part, it["path"])
                        it["status"] = "concluido"
                        it["total"] = it["done"]
                        it["finished"] = int(time.time())
        except Exception as e:
            msg = str(e)
            if isinstance(e, urllib.error.URLError):
                msg = "sem conexão com o provedor (%s)" % e.reason
            elif isinstance(e, (socket.timeout, TimeoutError)):
                msg = "o provedor parou de responder - clique em Retomar"
            with self.lock:
                it.pop("speed", None)
                if it["status"] == "baixando":
                    it["status"], it["msg"] = "erro", msg
        finally:
            with self.lock:
                self.workers.pop(it["id"], None)
            self.save()
            self.pump()


DL = None


def open_folder(path):
    path = path if os.path.isdir(path) else os.path.dirname(path)
    os.makedirs(path, exist_ok=True)
    if os.name == "nt":
        os.startfile(path)
    elif sys.platform == "darwin":
        import subprocess
        subprocess.Popen(["open", path])
    else:
        import subprocess
        subprocess.Popen(["xdg-open", path])


MIME = {".mp4": "video/mp4", ".m4v": "video/mp4", ".mkv": "video/x-matroska", ".webm": "video/webm",
        ".avi": "video/x-msvideo", ".ts": "video/mp2t", ".mov": "video/quicktime", ".flv": "video/x-flv"}


# ---------------------------------------------------------------- servidor HTTP
class Handler(BaseHTTPRequestHandler):
    server_version = "BergaTV/" + VERSION

    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype="application/json; charset=utf-8", extra=None):
        if isinstance(body, str):
            body = body.encode("utf-8")
        gz = len(body) > 2048 and "gzip" in (self.headers.get("Accept-Encoding") or "")
        if gz:
            body = gzip.compress(body, 5)
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("Access-Control-Allow-Origin", "*")
        if gz:
            self.send_header("Content-Encoding", "gzip")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def _err(self, code, msg):
        self._send(code, json.dumps({"erro": msg}, ensure_ascii=False))

    def do_GET(self):
        p = urllib.parse.urlsplit(self.path)
        qs = urllib.parse.parse_qs(p.query)
        g = lambda k: (qs.get(k) or [None])[0]
        try:
            if p.path in ("/", "/index.html"):
                return self._send(200, HTML, "text/html; charset=utf-8")
            if p.path == "/ping":
                return self._send(200, '{"ok":true,"versao":"%s"}' % VERSION)
            if not g("u") and p.path in ("/t", "/p", "/epg"):
                return self._err(400, "parametro u ausente")
            if p.path == "/t":
                return self.text(g("u"), g("ua"))
            if p.path == "/p":
                return self.stream(g("u"), g("ua"))
            if p.path == "/epg":
                return self._send(200, epg_json(g("u"), g("ua"), bool(g("force"))))
            if p.path == "/dl/list":
                return self._send(200, json.dumps(DL.snapshot(), ensure_ascii=False))
            if p.path.startswith("/dl/file/"):
                return self.local_file(p.path[9:].split(".")[0])
            if p.path == "/favicon.ico":
                return self._send(204, b"", "image/x-icon")
            self._err(404, "nao encontrado")
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            pass
        except Exception as e:
            msg = str(e)
            if isinstance(e, urllib.error.URLError):
                msg = "nao foi possivel conectar ao provedor (%s)" % e.reason
            if isinstance(e, (socket.timeout, TimeoutError)):
                msg = "o provedor demorou demais para responder"
            try:
                self._err(502, msg or e.__class__.__name__)
            except Exception:
                pass

    def do_OPTIONS(self):
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type, Range")
        self.send_header("Access-Control-Max-Age", "86400")
        self.end_headers()

    def do_POST(self):
        p = urllib.parse.urlsplit(self.path)
        try:
            n = int(self.headers.get("Content-Length") or 0)
            body = json.loads(self.rfile.read(n).decode("utf-8") or "{}") if n else {}
            if p.path == "/dl/add":
                added = DL.add(body.get("items") or [], body.get("ua"))
                return self._send(200, json.dumps({"ok": True, "added": added}))
            if p.path == "/dl/act":
                return self._send(200, json.dumps({"ok": DL.act(body.get("id"), body.get("act"))}))
            if p.path == "/dl/config":
                DL.set_cfg(body.get("dir"), body.get("max"))
                return self._send(200, json.dumps({"ok": True}))
            if p.path == "/dl/open":
                it = DL.find(body.get("id")) if body.get("id") else None
                open_folder(it["path"] if it else DL.cfg["dir"])
                return self._send(200, json.dumps({"ok": True}))
            self._err(404, "nao encontrado")
        except Exception as e:
            try:
                self._err(500, str(e) or e.__class__.__name__)
            except Exception:
                pass

    def local_file(self, did):
        it = DL.find(did)
        if not it or it["status"] != "concluido" or not os.path.exists(it["path"]):
            return self._err(404, "arquivo nao encontrado - pode ter sido apagado ou movido")
        size = os.path.getsize(it["path"])
        start, end = 0, size - 1
        m = re.match(r"bytes=(\d*)-(\d*)", self.headers.get("Range") or "")
        if m and (m.group(1) or m.group(2)):
            if m.group(1):
                start = int(m.group(1))
                end = int(m.group(2)) if m.group(2) else size - 1
            else:
                start = max(0, size - int(m.group(2)))
            end = min(end, size - 1)
            if start > end:
                self.send_response(416)
                self.send_header("Content-Range", "bytes */%d" % size)
                self.end_headers()
                return
            self.send_response(206)
            self.send_header("Content-Range", "bytes %d-%d/%d" % (start, end, size))
        else:
            self.send_response(200)
        self.send_header("Content-Type", MIME.get(it["ext"], "application/octet-stream"))
        self.send_header("Accept-Ranges", "bytes")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Expose-Headers", "Content-Length, Content-Range, Accept-Ranges")
        self.send_header("Content-Length", str(end - start + 1))
        self.end_headers()
        if self.command == "HEAD":
            return
        with open(it["path"], "rb") as f:
            f.seek(start)
            left = end - start + 1
            while left > 0:
                chunk = f.read(min(262144, left))
                if not chunk:
                    break
                self.wfile.write(chunk)
                left -= len(chunk)

    def text(self, url, ua):
        r = upstream(url, ua, timeout=120)
        try:
            data = r.read()
        finally:
            r.close()
        if data[:2] == b"\x1f\x8b":
            data = gzip.decompress(data)
        code = r.getcode()
        if code >= 400:
            return self._err(code, "o provedor respondeu HTTP %d" % code)
        self._send(code, data, "text/plain; charset=utf-8")

    def stream(self, url, ua):
        r = upstream(url, ua, self.headers.get("Range"), timeout=30)
        try:
            code = r.getcode()
            if code >= 400:
                r.read(4096)
                return self._err(code, "o provedor respondeu HTTP %d" % code)
            first = r.read(2048)
            if first.lstrip(b"\xef\xbb\xbf \r\n\t").startswith(b"#EXTM3U"):
                data = first + r.read(16 * 1024 * 1024)
                txt = data.decode("utf-8", "replace")
                if "#EXT-X-" in txt or "#EXTINF" in txt:
                    return self._send(code, rewrite_m3u8(txt, r.geturl(), ua), "application/vnd.apple.mpegurl")
                return self._send(code, data, "text/plain; charset=utf-8")
            self.send_response(code)
            ct = r.headers.get("Content-Type") or "application/octet-stream"
            path = urllib.parse.urlsplit(r.geturl()).path.lower()
            if path.endswith(".ts") and "mpegurl" not in ct.lower():
                ct = "video/mp2t"
            self.send_header("Content-Type", ct)
            for h in ("Content-Length", "Content-Range", "Accept-Ranges", "Last-Modified"):
                v = r.headers.get(h)
                if v:
                    self.send_header(h, v)
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(first)
            reader = getattr(r, "read1", None) or r.read
            while True:
                chunk = reader(65536)
                if not chunk:
                    break
                self.wfile.write(chunk)
        finally:
            try:
                r.close()
            except Exception:
                pass


class Server(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = os.name != "nt"  # no Windows isso permitiria abrir duas vezes na mesma porta


def lan_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        return "IP-DESTE-PC"


def main():
    args = sys.argv[1:]
    port = 8765
    if "--port" in args:
        try:
            port = int(args[args.index("--port") + 1])
        except (IndexError, ValueError):
            print("Uso: --port 9000")
            return
    lan = "--lan" in args
    host = "0.0.0.0" if lan else "127.0.0.1"
    url = "http://127.0.0.1:%d/" % port
    global DL
    try:
        srv = Server((host, port), Handler)
    except OSError:
        print("A porta %d ja esta em uso - o Berga TV provavelmente ja esta aberto." % port)
        print("Abrindo %s" % url)
        if "--no-browser" not in args:
            webbrowser.open(url)
        time.sleep(2)
        return
    DL = Downloads()
    print("=" * 56)
    print("  Berga TV %s rodando" % VERSION)
    print("  Neste PC:      %s" % url)
    if lan:
        print("  TV / celular:  http://%s:%d/  (mesma rede Wi-Fi)" % (lan_ip(), port))
    print("  Downloads em:  %s" % DL.cfg["dir"])
    print("  Deixe esta janela aberta enquanto assiste ou baixa.")
    print("  Para fechar: Ctrl+C ou feche esta janela.")
    print("=" * 56)
    if "--no-browser" not in args:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nEncerrado.")


HTML = r'''<!doctype html>
<html lang="pt-BR">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Berga TV</title>
<script src="https://cdn.jsdelivr.net/npm/hls.js@1.7.3/dist/hls.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/mpegts.js@1.8.2/dist/mpegts.js"></script>
<style>
:root{--bg:#0c0e13;--bg2:#12151d;--bg3:#1a1f2b;--bg4:#232a39;--line:#252b3a;--tx:#e9ecf3;--tx2:#98a1b5;--ac:#ff5a1f;--ac2:#ff8148;--gold:#ffc53d;--r:10px}
*{box-sizing:border-box}
html,body{margin:0;height:100%;-webkit-tap-highlight-color:transparent;background:var(--bg);color:var(--tx);font:14px/1.4 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;overflow:hidden}
button{font:inherit;color:inherit;cursor:pointer}
input,select{font:inherit;color:var(--tx)}
::-webkit-scrollbar{width:10px;height:10px}::-webkit-scrollbar-thumb{background:#2c3446;border-radius:6px;border:2px solid transparent;background-clip:padding-box}::-webkit-scrollbar-track{background:transparent}
img:not([src]){visibility:hidden}img.noimg{visibility:hidden}
.muted{color:var(--tx2)}.small{font-size:12px}
.top{height:58px;display:flex;align-items:center;gap:14px;padding:0 16px;background:var(--bg2);border-bottom:1px solid var(--line)}
.brand{display:flex;align-items:center;gap:9px;font-size:17px;white-space:nowrap;letter-spacing:.2px}
.brand .logo{width:32px;height:32px;border-radius:9px;background:linear-gradient(135deg,var(--ac),#ff9a3c);display:grid;place-items:center;font-weight:800;color:#fff}
.brand b{color:var(--ac)}
nav{display:flex;gap:4px}
nav button{background:none;border:0;padding:8px 13px;border-radius:8px;color:var(--tx2);font-weight:600}
nav button:hover,nav button:focus-visible{background:var(--bg3);color:var(--tx);outline:none}
nav button.on{background:var(--ac);color:#fff}
.search{flex:1;max-width:360px;margin-left:auto}
.search input{width:100%;background:var(--bg3);border:1px solid var(--line);border-radius:8px;padding:9px 12px;outline:none}
.search input:focus{border-color:var(--ac)}
.status{color:var(--tx2);font-size:12px;white-space:nowrap;max-width:280px;overflow:hidden;text-overflow:ellipsis;display:flex;align-items:center;gap:6px}
.spin{width:12px;height:12px;border:2px solid var(--line);border-top-color:var(--ac);border-radius:50%;animation:sp 0.8s linear infinite;flex:none}
@keyframes sp{to{transform:rotate(360deg)}}
.icon{background:var(--bg3);border:1px solid var(--line);border-radius:8px;width:38px;height:38px;font-size:18px;flex:none}
.icon:hover{border-color:var(--ac)}
body{display:flex;flex-direction:column}
.top{flex:none}
main{position:relative;flex:1;min-height:0}
.view{position:absolute;top:0;right:0;bottom:0;left:0;display:none}
.view.on{display:flex}
.cats{width:230px;flex:none;overflow:auto;border-right:1px solid var(--line);background:var(--bg2);padding:8px}
.cat{display:flex;justify-content:space-between;gap:8px;padding:8px 10px;border-radius:8px;cursor:pointer;color:var(--tx2)}
.cat span:first-child{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.cat:hover,.cat:focus{background:var(--bg3);color:var(--tx);outline:none}
.cat.on{background:rgba(255,90,31,.15);color:var(--ac2)}
.cat .n{font-size:12px;opacity:.7;flex:none}
.list{width:390px;flex:none;overflow:auto;border-right:1px solid var(--line)}
.ch{display:flex;align-items:center;gap:10px;padding:8px 10px 8px 6px;border-bottom:1px solid var(--line);cursor:pointer}
.ch:hover,.ch:focus{background:var(--bg3);outline:none}
.ch.on{background:rgba(255,90,31,.12);box-shadow:inset 3px 0 var(--ac)}
.num{width:36px;color:var(--tx2);font-size:12px;text-align:right;flex:none}
.chlogo{width:54px;height:36px;object-fit:contain;flex:none;border-radius:6px}
.chtxt{flex:1;min-width:0}
.chname{font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.chnow{font-size:12px;color:var(--tx2);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;min-height:16px}
.bar{height:3px;background:var(--line);border-radius:2px;margin-top:4px;overflow:hidden}
.bar i{display:block;height:100%;background:var(--ac);width:0}
.bar.big{height:5px;margin-top:8px}
.star{position:relative;background:none;border:0;color:#3b4254;font-size:23px;padding:2px 2px;line-height:1}
.star i{position:absolute;left:0;right:0;top:50%;margin-top:-4px;font-size:9.5px;font-style:normal;font-weight:900;color:#c9cfdb;line-height:1;text-align:center;text-shadow:none}
.star.on i{color:#14161c}
.star:hover{color:#8a92a8}.star.on{color:var(--gold)}.star[data-w=f].on{color:#ff6fae}
.stars{display:inline-flex;flex:none}
.favTabs{display:flex;margin-bottom:6px}.favTabs button{margin-right:8px}
.gProg{cursor:pointer}.gProg.cu b:before{content:'⏪ ';color:var(--ac2)}.gProg.rec b:before{content:'⏺ ';color:#ff4d4d}
.gName{cursor:pointer}
.arcDay{margin:16px 0 6px;color:var(--tx2);font-size:12px;text-transform:uppercase;letter-spacing:.8px}
.arcRow{display:flex;align-items:center;padding:9px 10px;border-radius:8px;cursor:pointer}
.arcRow:hover,.arcRow:focus{background:var(--bg3);outline:none}
.arcRow .t{color:var(--ac2);width:54px;flex:none;font-variant-numeric:tabular-nums}.arcRow .d{color:var(--tx2);font-size:12px;margin-left:auto;padding-left:10px;flex:none}
.ep{cursor:pointer}.ep.rec span:last-child:before{content:'⏺ ';color:#ff4d4d}
.sentinel{height:1px;grid-column:1/-1}
.playerPane{flex:1;min-width:0;display:flex;flex-direction:column;overflow:auto;padding:16px;gap:14px}
.videoWrap{position:relative;background:#000;border-radius:var(--r);overflow:hidden;aspect-ratio:16/9;flex:none;max-height:62vh}
.videoWrap video,.vodPlayer video{width:100%;height:100%;display:block;background:#000}
.vmsg{position:absolute;top:0;right:0;bottom:0;left:0;display:none;align-items:center;justify-content:center;text-align:center;padding:24px;color:#fff;background:#000b;pointer-events:none;font-size:15px}
.vmsg.on{display:flex}
.niTop{display:flex;gap:14px;align-items:flex-start}
.niTop img{width:72px;height:50px;object-fit:contain;flex:none;border-radius:8px;background:var(--bg3)}
.niTop .grow{flex:1;min-width:0}
.niName{font-size:18px;font-weight:700}
.niProg{font-size:15px;margin-top:2px}
.niTime{font-size:12px;color:var(--tx2)}
.desc{color:var(--tx2);margin:8px 0 0}
.epList h4{margin:4px 0 8px;color:var(--tx2);font-size:12px;text-transform:uppercase;letter-spacing:.8px}
.ep{display:flex;gap:12px;padding:7px 0;border-bottom:1px solid var(--line)}
.ep .t{color:var(--ac2);width:46px;flex:none;font-variant-numeric:tabular-nums}
.btn{background:var(--bg3);border:1px solid var(--line);border-radius:8px;padding:9px 14px;font-weight:600;white-space:nowrap}
.btn:hover,.btn:focus-visible{border-color:var(--ac);outline:none}
.btn.pri{background:var(--ac);border-color:var(--ac);color:#fff}
.btn.pri:hover{background:var(--ac2)}
.btn.sm{padding:5px 10px;font-size:12px}
.btn.danger:hover{border-color:#e5484d;color:#ff8a8d}
.grid{flex:1;overflow:auto;padding:18px;display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:18px 14px;align-content:start}
.card{cursor:pointer;border-radius:10px;outline:none}
.card .poster{position:relative;aspect-ratio:2/3;background:var(--bg3);border-radius:10px;overflow:hidden;transition:transform .15s}
.card:hover .poster,.card:focus .poster{transform:translateY(-3px);box-shadow:0 0 0 2px var(--ac)}
.poster img{position:absolute;top:0;right:0;bottom:0;left:0;width:100%;height:100%;object-fit:cover}
.poster .ph{position:absolute;top:0;right:0;bottom:0;left:0;display:grid;place-items:center;padding:10px;text-align:center;color:var(--tx2);font-size:13px}
.poster .rate{position:absolute;left:6px;top:6px;background:#000c;border-radius:6px;padding:2px 6px;font-size:11px;color:var(--gold)}
.poster .stars{position:absolute;right:2px;top:2px}.poster .star{text-shadow:0 1px 3px #000}
.poster .pbar{position:absolute;left:0;right:0;bottom:0;margin:0;height:4px;border-radius:0}
.ctitle{margin-top:7px;font-size:13px;line-height:1.3;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.guideWrap{flex:1;display:flex;flex-direction:column;min-width:0}
.guideBar{display:flex;gap:10px;align-items:center;padding:10px 16px;border-bottom:1px solid var(--line);background:var(--bg2)}
select{background:var(--bg3);border:1px solid var(--line);border-radius:8px;padding:8px 10px;max-width:320px}
.guide{flex:1;overflow:auto;position:relative}
.gInner{position:relative}
.gHead{display:flex;position:sticky;top:0;z-index:4;background:var(--bg2);border-bottom:1px solid var(--line);height:34px}
.gCorner{width:210px;flex:none;position:sticky;left:0;background:var(--bg2);z-index:5;padding:8px 12px;font-size:12px;color:var(--tx2)}
.gRuler{position:relative;flex:none}
.gRuler span{position:absolute;top:8px;font-size:12px;color:var(--tx2);padding-left:6px;border-left:1px solid var(--line)}
.gRow{display:flex;height:58px;border-bottom:1px solid var(--line);cursor:pointer}
.gRow:hover .gName{background:var(--bg3)}
.gName{width:210px;flex:none;position:sticky;left:0;z-index:2;background:var(--bg2);display:flex;align-items:center;gap:8px;padding:0 10px;border-right:1px solid var(--line)}
.gName img{width:40px;height:28px;object-fit:contain;flex:none}
.gName span{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-weight:600;font-size:13px}
.gTrack{position:relative;flex:none}
.gProg{position:absolute;top:5px;bottom:5px;background:var(--bg3);border-radius:6px;padding:5px 8px;overflow:hidden;white-space:nowrap;border:1px solid var(--line)}
.gProg b{display:block;font-size:12px;overflow:hidden;text-overflow:ellipsis;font-weight:600}
.gProg small{color:var(--tx2);font-size:11px}
.gProg.live{background:rgba(255,90,31,.16);border-color:rgba(255,90,31,.5)}
.gProg.empty{color:var(--tx2);font-size:12px;background:none;border-style:dashed}
.gNow{position:absolute;top:0;bottom:0;width:2px;background:var(--ac);z-index:3;pointer-events:none}
.favBox{flex:1;overflow:auto;padding:18px 22px}
.favBox h3{margin:22px 0 12px;font-size:15px;color:var(--tx2);text-transform:uppercase;letter-spacing:.8px}
.favBox h3:first-child{margin-top:0}
.favBox .grid{padding:0;overflow:visible}
.chips{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:8px}
.chips .ch{border:1px solid var(--line);border-radius:10px}
.emptyState{position:absolute;top:0;right:0;bottom:0;left:0;display:none;align-items:center;justify-content:center;z-index:5;background:var(--bg)}
.emptyState.on{display:flex}
.emptyCard{max-width:460px;text-align:center;padding:30px}
.emptyCard .logo{width:64px;height:64px;font-size:30px;margin:0 auto 16px;border-radius:16px;background:linear-gradient(135deg,var(--ac),#ff9a3c);display:grid;place-items:center;font-weight:800;color:#fff}
.modal{position:fixed;top:0;right:0;bottom:0;left:0;background:#000b;z-index:50;display:flex;align-items:flex-start;justify-content:center;overflow:auto;padding:40px 16px}
.modal.hidden,.hidden{display:none!important}
.modalCard{position:relative;background:var(--bg2);border:1px solid var(--line);border-radius:14px;width:min(860px,100%);padding:24px;box-shadow:0 20px 60px #000a}
.modalCard h2{margin:0 0 6px}.modalCard h3{margin:22px 0 10px;font-size:14px;text-transform:uppercase;letter-spacing:.8px;color:var(--tx2)}
.mx{position:absolute;right:12px;top:12px;background:var(--bg3);border:1px solid var(--line);border-radius:8px;width:34px;height:34px;z-index:2}
.mHead{display:flex;gap:20px;position:relative}
.mBack{position:absolute;top:-24px;left:-24px;right:-24px;height:260px;background:var(--bd) center/cover;opacity:.18;border-radius:14px 14px 0 0;mask-image:linear-gradient(#000,transparent);-webkit-mask-image:linear-gradient(#000,transparent);pointer-events:none}
.mPoster{width:180px;aspect-ratio:2/3;object-fit:cover;border-radius:10px;flex:none;background:var(--bg3);position:relative}
.mMeta{flex:1;min-width:0;position:relative}
.tags{display:flex;flex-wrap:wrap;gap:6px;margin:6px 0 12px}
.tags span{background:var(--bg4);border-radius:6px;padding:3px 8px;font-size:12px;color:var(--tx2)}
.mBtns{display:flex;gap:8px;flex-wrap:wrap;margin-top:16px}
.seasons{display:flex;gap:6px;flex-wrap:wrap;margin:18px 0 10px}
.seasons button{background:var(--bg3);border:1px solid var(--line);border-radius:8px;padding:6px 12px}
.seasons button.on{background:var(--ac);border-color:var(--ac);color:#fff}
.epi{display:flex;gap:12px;align-items:center;padding:10px;border-radius:10px;cursor:pointer;border:1px solid transparent}
.epi:hover,.epi:focus{background:var(--bg3);border-color:var(--line);outline:none}
.epi img{width:120px;aspect-ratio:16/9;object-fit:cover;border-radius:6px;background:var(--bg4);flex:none}
.epi .en{color:var(--ac2);font-weight:700;width:36px;flex:none;text-align:center}
.epi .et{flex:1;min-width:0}
.epi .et b{display:block}
.epi .et p{margin:3px 0 0;color:var(--tx2);font-size:12px;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.src{display:flex;justify-content:space-between;align-items:center;gap:10px;padding:12px;border:1px solid var(--line);border-radius:10px;margin-bottom:8px}
.src.on{border-color:var(--ac)}
.src>div:first-child{min-width:0}.src .muted{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.srcBtns{display:flex;gap:6px;flex-wrap:wrap;justify-content:flex-end;flex:none}
.pill{background:rgba(255,90,31,.15);color:var(--ac2);border-radius:20px;padding:4px 10px;font-size:12px;font-weight:600}
.tabs{display:flex;gap:6px;margin-bottom:12px}
.tabs button{background:var(--bg3);border:1px solid var(--line);border-radius:8px;padding:7px 14px;font-weight:600}
.tabs button.on{border-color:var(--ac);color:var(--ac2)}
form label{display:block;margin-bottom:10px;font-size:13px;color:var(--tx2)}
form input:not([type=checkbox]):not([type=file]),form select{display:block;width:100%;max-width:none;margin-top:4px;background:var(--bg3);border:1px solid var(--line);border-radius:8px;padding:9px 11px;outline:none}
form input:focus{border-color:var(--ac)}
form input[type=file]{display:block;margin-top:6px;color:var(--tx2)}
.row2{display:grid;grid-template-columns:1fr 1fr;gap:10px}
form[data-type=m3u] .only-xtream,form[data-type=xtream] .only-m3u{display:none}
.chk{display:flex!important;align-items:center;gap:8px;color:var(--tx)!important}
.acct{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:8px}
.acct div{background:var(--bg3);border-radius:8px;padding:10px}.acct b{display:block;font-size:15px}
.vodPlayer{position:fixed;top:0;right:0;bottom:0;left:0;background:#000;z-index:60}
.vodTop{position:absolute;left:0;right:0;top:0;display:flex;align-items:center;gap:12px;padding:12px 16px;background:linear-gradient(#000d,transparent);transition:opacity .3s;z-index:2}
.vodTop span{flex:1;font-weight:700;font-size:16px}
.vodPlayer.idle .vodTop{opacity:0}
.toast{position:fixed;left:50%;bottom:22px;transform:translateX(-50%);background:var(--bg4);border:1px solid var(--line);border-radius:10px;padding:11px 16px;z-index:90;max-width:min(560px,90vw);box-shadow:0 10px 30px #0008;display:none}
.toast.on{display:block}.toast.err{border-color:#e5484d}
.mini{position:fixed;right:20px;bottom:20px;width:400px;z-index:40;background:#000;border-radius:12px;overflow:hidden;box-shadow:0 12px 40px #000c;border:1px solid var(--line);display:none;resize:horizontal;min-width:260px;max-width:90vw}
.mini.on{display:block}
.miniBar{display:flex;align-items:center;gap:6px;padding:6px 8px;background:var(--bg2);cursor:move;user-select:none;touch-action:none}
.miniBar span{flex:1;font-weight:600;font-size:13px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.miniBar button,.mvLbl button{background:var(--bg3);border:1px solid var(--line);border-radius:6px;min-width:28px;height:26px;font-size:13px;padding:0 6px}
.miniBar button:hover,.mvLbl button:hover{border-color:var(--ac)}
.mini .videoWrap{border-radius:0;max-height:none}
.mvWrap{flex:1;display:flex;flex-direction:column;min-width:0;background:#000}
.mvWrap:fullscreen .guideBar{display:none}
.mvGrid{flex:1;display:grid;gap:6px;padding:6px;grid-template-columns:1fr 1fr;grid-template-rows:1fr 1fr;min-height:0}
.mvGrid.l13{grid-template-columns:3fr 1fr;grid-template-rows:1fr 1fr 1fr}
.mvGrid.l13 .mvCell:first-child{grid-row:1/4}
.mvCell{position:relative;background:#0b0d12;border-radius:8px;overflow:hidden;border:2px solid #1b2030;min-height:0;cursor:pointer}
.mvCell:hover{border-color:#39415a}
.mvCell.aud{border-color:var(--ac)}
.mvCell video{position:absolute;top:0;right:0;bottom:0;left:0;width:100%;height:100%;object-fit:contain;background:#000}
.mvCell:fullscreen{border:0;border-radius:0}
.mvLbl{position:absolute;left:0;right:0;top:0;display:flex;align-items:center;gap:6px;padding:6px 8px;background:linear-gradient(#000d,transparent);opacity:0;transition:opacity .2s;z-index:3}
.mvCell:hover .mvLbl{opacity:1}
.mvLbl span{flex:1;font-weight:600;font-size:13px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.mvAdd{position:absolute;top:0;right:0;bottom:0;left:0;display:grid;place-items:center;text-align:center;color:var(--tx2);font-size:14px;z-index:2}
.mvAdd b{display:block;font-size:44px;line-height:1;color:var(--ac);margin-bottom:6px}
.mvAud{position:absolute;right:8px;bottom:8px;background:#000b;border-radius:6px;padding:2px 7px;font-size:12px;z-index:3;display:none}
.mvCell.aud .mvAud{display:block}
.mvCell .vmsg{font-size:13px}
.pkList{max-height:58vh;overflow:auto;border:1px solid var(--line);border-radius:10px}
.pkIn{width:100%;background:var(--bg3);border:1px solid var(--line);border-radius:8px;padding:9px 11px;outline:none}
.pkIn:focus{border-color:var(--ac)}
.badge{display:none;background:var(--ac);color:#fff;border-radius:10px;font-size:11px;padding:0 6px;margin-left:4px;line-height:16px;vertical-align:1px}
nav button.on .badge{background:#fff;color:var(--ac)}
.dlHead{display:flex;flex-wrap:wrap;gap:10px;align-items:center;margin-bottom:6px;padding:12px;border:1px solid var(--line);border-radius:10px;background:var(--bg2)}
.dlHead .path{flex:1;min-width:200px;font-size:13px;word-break:break-all}
.dlRow{display:flex;gap:14px;align-items:center;padding:12px;border:1px solid var(--line);border-radius:10px;margin-bottom:8px;background:var(--bg2)}
.dlRow img{width:46px;height:68px;object-fit:cover;border-radius:6px;background:var(--bg3);flex:none}
.dlMain{flex:1;min-width:0}
.dlMain b{display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.dlMain .bar{height:6px;margin:8px 0 6px}
.dlSt{font-size:12px;color:var(--tx2)}
.dlSt.err{color:#ff8a8d}
.dlBtns{display:flex;gap:6px;flex-wrap:wrap;justify-content:flex-end;flex:none}
.epi .dlb{flex:none}
.epi .dlb.ok{color:#5bd68a;border-color:#2c5a3f}
.pub{display:flex;justify-content:space-between;align-items:center;gap:10px;padding:10px 12px;border:1px dashed var(--line);border-radius:10px;margin-bottom:8px}
@media (max-width:1100px){.list{width:320px}.cats{width:190px}nav button{padding:8px 8px}.status{display:none}}
@media (max-width:1250px){.status{display:none}}
@supports not (aspect-ratio:1/1){
 .videoWrap{height:0;padding-bottom:56.25%;max-height:none}.videoWrap video{position:absolute;top:0;left:0}
 .card .poster{height:0;padding-bottom:150%}
 .mPoster{height:270px}.epi img{height:68px}
 nav button,.mBtns .btn,.srcBtns .btn,.dlBtns .btn,.tags span,.mvLbl button,.miniBar button{margin-right:6px}
 .top>*{margin-right:12px}
}
.tv :focus{outline:3px solid var(--ac)!important;outline-offset:-3px}
.tv .card:focus{outline:none!important}.tv .card:focus .poster{box-shadow:0 0 0 3px var(--ac);transform:scale(1.04)}
.tv .ch:focus,.tv .cat:focus,.tv .epi:focus,.tv .gRow:focus .gName{background:rgba(255,90,31,.22)}
.android .search input{font-size:16px}
html.webos #nav [data-view=dl],html.webos #nav [data-view=multi],html.webos [data-a=dl],html.webos .dlb,html.webos [data-a=dlseason],html.webos [data-a=pip],html.webos [data-m=pip]{display:none!important}
#osk{position:fixed;left:0;right:0;bottom:0;z-index:95;background:var(--bg2);border-top:2px solid var(--ac);padding:14px 18px 18px;box-shadow:0 -10px 40px #000c}
#osk.hidden{display:none}
.oskTop{display:flex;align-items:center;margin-bottom:10px}
.oskLbl{color:var(--tx2);font-size:13px;margin-right:12px;white-space:nowrap}
.oskVal{flex:1;min-height:44px;background:var(--bg3);border:1px solid var(--line);border-radius:8px;padding:10px 12px;font-size:20px;word-break:break-all;color:var(--tx)}
.oskVal:after{content:'|';color:var(--ac);margin-left:1px}
.oskRow{display:flex;justify-content:center;margin-top:6px}
.oskRow button{min-width:62px;height:50px;margin:0 3px;background:var(--bg4);border:1px solid var(--line);border-radius:8px;font-size:19px;color:var(--tx)}
.oskRow button.w2{min-width:130px}.oskRow button.w4{min-width:300px}
.oskRow button.ok{background:var(--ac);border-color:var(--ac);color:#fff}
.oskRow button:focus{outline:3px solid #fff!important;background:var(--ac);color:#fff}
@media (max-width:900px){
 .top{height:auto;flex-wrap:wrap;padding:8px 10px;gap:8px}
 .brand span:last-child{display:none}
 .search{order:2;flex:1;max-width:none;margin-left:0}
 #btnSettings{order:3}
 nav{order:4;width:100%;overflow-x:auto;scrollbar-width:none}
 nav::-webkit-scrollbar{display:none}
 nav button{flex:none;padding:7px 11px}
 #v-live.on,#v-movie.on,#v-series.on{flex-direction:column}
 .cats{width:auto;flex:none;display:flex;gap:6px;overflow-x:auto;overflow-y:hidden;border-right:0;border-bottom:1px solid var(--line);padding:8px 10px;scrollbar-width:none}
 .cats::-webkit-scrollbar{display:none}
 .cat{flex:none;padding:6px 12px;background:var(--bg3);border-radius:20px}
 .cat .n{display:none}
 #v-live .playerPane{order:-1;flex:none;padding:0;gap:0;overflow:visible}
 #v-live .videoWrap{border-radius:0;max-height:38vh;width:100%}
 #liveInfo{padding:8px 12px}#liveEpg,#liveInfo .desc,#liveInfo .niTop img{display:none}
 .niName{font-size:15px}.niProg{font-size:13px}
 .list{width:auto;flex:1;border-right:0}
 .grid{grid-template-columns:repeat(auto-fill,minmax(105px,1fr));gap:12px 10px;padding:12px}
 .gCorner,.gName{width:120px}
 .modal{padding:0}
 .modalCard{border-radius:0;min-height:100%;padding:18px 14px}
 .mHead{flex-direction:column;gap:12px}.mPoster{width:120px}
 .epi{flex-wrap:wrap}.epi img{width:96px}
 .mini{width:58vw;right:10px;bottom:10px}
 .row2{grid-template-columns:1fr}
 .src{flex-direction:column;align-items:flex-start}.srcBtns{justify-content:flex-start}
 .favBox{padding:12px}
 .chips{grid-template-columns:1fr}
 .dlRow{flex-wrap:wrap}.dlBtns{width:100%;justify-content:flex-start}
 .guideBar{flex-wrap:wrap}
 #v-multi .guideBar .muted{display:none}
 .mvLbl{opacity:1}
}
</style>
</head>
<body>
<header class="top">
  <div class="brand"><span class="logo">B</span><span>Berga <b>TV</b></span></div>
  <nav id="nav">
    <button data-view="live">Ao vivo</button>
    <button data-view="guide">Guia</button>
    <button data-view="movie">Filmes</button>
    <button data-view="series">Séries</button>
    <button data-view="multi">Multitela</button>
    <button data-view="fav">Favoritos</button>
    <button data-view="rec">Gravações<span class="badge" id="recBadge"></span></button>
    <button data-view="dl">Downloads<span class="badge" id="dlBadge"></span></button>
  </nav>
  <div class="search"><input id="q" placeholder="Buscar canal, filme ou série…" autocomplete="off"></div>
  <div id="status" class="status"></div>
  <button id="btnSettings" class="icon" title="Configurações">⚙</button>
</header>
<main>
  <section id="v-live" class="view">
    <aside class="cats" id="liveCats"></aside>
    <div class="list" id="liveList"></div>
    <div class="playerPane" id="livePane">
      <div class="videoWrap" id="liveWrap"><video id="liveVideo" controls playsinline></video><div class="vmsg" id="liveMsg"></div></div>
      <div id="liveInfo"></div>
      <div class="epList" id="liveEpg"></div>
    </div>
  </section>
  <section id="v-guide" class="view">
    <div class="guideWrap">
      <div class="guideBar"><select id="guideCat"></select><button class="btn sm" id="guideNow">Agora</button><span class="muted small" id="guideNote"></span></div>
      <div class="guide" id="guide"></div>
    </div>
  </section>
  <section id="v-movie" class="view"><aside class="cats" id="movieCats"></aside><div class="grid" id="movieGrid"></div></section>
  <section id="v-series" class="view"><aside class="cats" id="seriesCats"></aside><div class="grid" id="seriesGrid"></div></section>
  <section id="v-multi" class="view"><div class="mvWrap" id="mvWrap">
    <div class="guideBar"><b>Multitela</b><span class="muted small">Clique num quadro para ouvir o som dele · duplo clique = tela cheia · teclas 1 a 4 trocam o som</span><span style="flex:1"></span><button class="btn sm" data-l="4">▦ 2×2</button><button class="btn sm" data-l="13">◧ 1 + 3</button><button class="btn sm" id="mvFs">⛶ Tela cheia</button><button class="btn sm danger" id="mvClear">Limpar</button></div>
    <div class="mvGrid" id="mvGrid"></div>
  </div></section>
  <section id="v-fav" class="view"><div class="favBox" id="favBox"></div></section>
  <section id="v-dl" class="view"><div class="favBox" id="dlBox"></div></section>
  <section id="v-rec" class="view"><div class="favBox" id="recBox"></div></section>
  <div class="emptyState" id="empty"><div class="emptyCard"><div class="logo">B</div><h2>Bem-vindo ao Berga TV</h2><p class="muted">Adicione sua lista M3U ou seu login Xtream Codes para começar.</p><button class="btn pri" id="emptyAdd">+ Adicionar lista</button></div></div>
</main>
<div id="modal" class="modal hidden"><div class="modalCard" id="modalCard"></div></div>
<div id="vodPlayer" class="vodPlayer hidden">
  <video id="vodVideo" controls playsinline></video>
  <div class="vodTop"><button class="btn" id="vodClose">← Voltar</button><span id="vodTitle"></span><button class="btn hidden" id="vodNext">Próximo episódio ▸</button></div>
  <div class="vmsg" id="vodMsg"></div>
</div>
<div id="mini" class="mini"><div class="miniBar" id="miniBar"><span id="miniName"></span><button data-m="live" title="Voltar ao vivo">⟳</button><button data-m="pip" title="Janela flutuante fora do navegador (Picture-in-Picture)">⧉</button><button data-m="back" title="Voltar para o canal">⤢</button><button data-m="close" title="Parar e fechar">✕</button></div><div id="miniSlot"></div></div>
<div id="osk" class="hidden"></div>
<div class="toast" id="toast"></div>

<script>
(function(){var A=Array.prototype;
if(!A.flat)A.flat=function(){return A.concat.apply([],this)};
if(!Object.values)Object.values=function(o){return Object.keys(o).map(function(k){return o[k]})};
if(!Object.entries)Object.entries=function(o){return Object.keys(o).map(function(k){return [k,o[k]]})};
if(!String.prototype.padStart)String.prototype.padStart=function(n,c){var s=String(this);c=c===undefined?' ':String(c);while(s.length<n)s=c+s;return s};
if(!window.ResizeObserver)window.ResizeObserver=function(){return{observe:function(){},disconnect:function(){}}};
window.addEventListener('error',function(e){if(window.__bergaOk)return;var d=document.createElement('div');d.style.cssText='position:fixed;left:0;right:0;bottom:0;z-index:999;background:#5a1414;color:#fff;padding:12px 16px;font:14px sans-serif';d.textContent='O navegador deste aparelho não conseguiu abrir o Berga TV ('+(e.message||'erro')+'). Mande uma foto desta tela para o suporte.';(document.body||document.documentElement).appendChild(d)});
})();
</script>
<script>
"use strict";
var __defProp = Object.defineProperty;
var __defProps = Object.defineProperties;
var __getOwnPropDescs = Object.getOwnPropertyDescriptors;
var __getOwnPropSymbols = Object.getOwnPropertySymbols;
var __hasOwnProp = Object.prototype.hasOwnProperty;
var __propIsEnum = Object.prototype.propertyIsEnumerable;
var __defNormalProp = (obj, key, value) => key in obj ? __defProp(obj, key, { enumerable: true, configurable: true, writable: true, value }) : obj[key] = value;
var __spreadValues = (a, b) => {
  for (var prop in b || (b = {}))
    if (__hasOwnProp.call(b, prop))
      __defNormalProp(a, prop, b[prop]);
  if (__getOwnPropSymbols)
    for (var prop of __getOwnPropSymbols(b)) {
      if (__propIsEnum.call(b, prop))
        __defNormalProp(a, prop, b[prop]);
    }
  return a;
};
var __spreadProps = (a, b) => __defProps(a, __getOwnPropDescs(b));
var __async = (__this, __arguments, generator) => {
  return new Promise((resolve, reject) => {
    var fulfilled = (value) => {
      try {
        step(generator.next(value));
      } catch (e) {
        reject(e);
      }
    };
    var rejected = (value) => {
      try {
        step(generator.throw(value));
      } catch (e) {
        reject(e);
      }
    };
    var step = (x) => x.done ? resolve(x.value) : Promise.resolve(x.value).then(fulfilled, rejected);
    step((generator = generator.apply(__this, __arguments)).next());
  });
};
const AND = window.BergaAndroid || null;
const WEBOS = window.BERGA_PLATFORM === "webos";
const TVBROWSER = !AND && (WEBOS || /web0s|webos|netcast|tizen|smart-?tv|hbbtv/i.test(navigator.userAgent));
const TV = !!(AND && AND.isTV && AND.isTV()) || TVBROWSER;
const $ = (s) => document.querySelector(s);
const enc = encodeURIComponent;
const esc = (s) => String(s != null ? s : "").replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]);
const norm = (s) => String(s || "").normalize("NFKD").replace(/[̀-ͯ]/g, "").toLowerCase().replace(/\b(fhd|uhd|hd|sd|4k|h265|hevc|alt)\b/g, " ").replace(/[^a-z0-9]/g, "");
const nowS = () => Date.now() / 1e3;
const hhmm = (t) => new Date(t * 1e3).toLocaleTimeString("pt-BR", { hour: "2-digit", minute: "2-digit" });
const fmtDur = (s) => {
  s = Math.max(0, Math.floor(s));
  const h = Math.floor(s / 3600), m = Math.floor(s % 3600 / 60), x = s % 60;
  return (h ? h + ":" + String(m).padStart(2, "0") : m) + ":" + String(x).padStart(2, "0");
};
const pct = (p) => Math.max(0, Math.min(100, (nowS() - p[0]) / (p[1] - p[0]) * 100));
const arr = (v) => Array.isArray(v) ? v : v && typeof v === "object" ? Object.values(v) : [];
const hostOf = (u) => {
  try {
    return new URL(/^https?:/i.test(u) ? u : "http://" + u).host;
  } catch (e) {
    return u;
  }
};
const ADULT = /(adult|xxx|\+ ?18|18 ?\+|porn)/i;
const LS = { get(k, d) {
  try {
    const v = localStorage.getItem("biptv." + k);
    return v == null ? d : JSON.parse(v);
  } catch (e) {
    return d;
  }
}, set(k, v) {
  try {
    localStorage.setItem("biptv." + k, JSON.stringify(v));
  } catch (e) {
    console.warn("localStorage", e);
  }
} };
const idb = {
  p: null,
  open() {
    return this.p || (this.p = new Promise((res, rej) => {
      const r = indexedDB.open("bergaiptv", 1);
      r.onupgradeneeded = () => r.result.createObjectStore("kv");
      r.onsuccess = () => res(r.result);
      r.onerror = () => rej(r.error);
    }));
  },
  run(mode, fn) {
    return __async(this, null, function* () {
      const db = yield this.open();
      return new Promise((res, rej) => {
        const tx = db.transaction("kv", mode);
        const rq = fn(tx.objectStore("kv"));
        tx.oncomplete = () => res(rq && rq.result);
        tx.onerror = () => rej(tx.error);
      });
    });
  },
  get(k) {
    return this.run("readonly", (s) => s.get(k));
  },
  set(k, v) {
    return this.run("readwrite", (s) => s.put(v, k));
  },
  del(k) {
    return this.run("readwrite", (s) => s.delete(k));
  }
};
const snap = (it) => JSON.parse(JSON.stringify(it, (k, v) => k[0] === "_" ? void 0 : v));
const S = {
  sources: LS.get("sources", []),
  active: LS.get("active", null),
  favs: LS.get("favs", {}),
  prog: LS.get("prog", {}),
  cfg: Object.assign({ ua: "", fmt: "auto", hideAdult: false, favF: "Fran", favB: "Berga", pcAddr: "" }, LS.get("cfg", {})),
  favTab: LS.get("favTab", "b"),
  items: { live: [], movie: [], series: [] },
  cat: { live: [], movie: [], series: [] },
  sel: { live: "*", movie: "*", series: "*" },
  view: LS.get("view", "live"),
  q: "",
  liveOn: false,
  nativeOpen: false,
  appPaused: false,
  nativeIts: {},
  mvAll: LS.get("mv", {}),
  src: null,
  x: null,
  acct: null,
  epg: null,
  epgTok: 0,
  epgLoad: 0,
  cur: null,
  vod: null,
  modalFor: null,
  guideCat: null
};
const uaQ = () => S.cfg.ua ? "&ua=" + enc(S.cfg.ua) : "";
const px = (u) => WEBOS ? u : "/p?u=" + enc(u) + uaQ();
function txt(u) {
  return __async(this, null, function* () {
    if (WEBOS) {
      let r2;
      try {
        r2 = yield fetch(u, { cache: "no-store" });
      } catch (e) {
        throw new Error("não foi possível conectar ao provedor");
      }
      if (!r2.ok) throw new Error("o provedor respondeu HTTP " + r2.status);
      return r2.text();
    }
    const r = yield fetch("/t?u=" + enc(u) + uaQ());
    const t = yield r.text();
    if (!r.ok) {
      let m = "HTTP " + r.status;
      try {
        m = JSON.parse(t).erro || m;
      } catch (e) {
      }
      throw new Error(m);
    }
    return t;
  });
}
const xapi = (a, extra = "") => `${S.x.base}/player_api.php?username=${enc(S.x.u)}&password=${enc(S.x.p)}&action=${a}${extra}`;
let toastT;
function toast(m, err) {
  const t = $("#toast");
  t.textContent = m;
  t.className = "toast on" + (err ? " err" : "");
  clearTimeout(toastT);
  toastT = setTimeout(() => t.className = "toast", err ? 7e3 : 4500);
}
function status(m, busy) {
  $("#status").innerHTML = (busy ? '<span class="spin"></span>' : "") + "<span>" + esc(m) + "</span>";
  $("#status").title = m || "";
}
function vmsg(which, m) {
  const e = $("#" + which + "Msg");
  e.textContent = m || "";
  e.classList.toggle("on", !!m);
}
function modal(html) {
  $("#modalCard").innerHTML = html;
  $("#modal").classList.remove("hidden");
}
function closeModal() {
  $("#modal").classList.add("hidden");
  $("#modalCard").innerHTML = "";
  $("#modalCard").onclick = null;
  $("#modalCard").onsubmit = null;
  S.modalFor = null;
}
function fs(el) {
  const d = document, fe = d.fullscreenElement || d.webkitFullscreenElement;
  if (fe) {
    (d.exitFullscreen || d.webkitExitFullscreen).call(d);
    return;
  }
  const rq = el.requestFullscreen || el.webkitRequestFullscreen;
  if (rq) {
    const r = rq.call(el);
    r && r.catch && r.catch(() => {
    });
  }
}
document.addEventListener("error", (e) => {
  if (e.target && e.target.tagName === "IMG") e.target.classList.add("noimg");
}, true);
function chunked(box, items, make, size = 120) {
  if (box._obs) box._obs.disconnect();
  box.innerHTML = "";
  const sen = document.createElement("div");
  sen.className = "sentinel";
  box.appendChild(sen);
  let i = 0;
  const add = () => {
    const f = document.createDocumentFragment();
    const end = Math.min(i + size, items.length);
    for (; i < end; i++) f.appendChild(make(items[i], i));
    box.insertBefore(f, sen);
    if (i >= items.length) {
      obs.disconnect();
      sen.remove();
    }
  };
  const obs = new IntersectionObserver((es) => {
    if (es.some((e) => e.isIntersecting)) add();
  }, { rootMargin: "600px" });
  box._obs = obs;
  add();
  if (i < items.length) obs.observe(sen);
}
const engines = /* @__PURE__ */ new WeakMap();
function stopVideo(v) {
  v._tok = (v._tok || 0) + 1;
  v._k = null;
  const e = engines.get(v);
  if (e) {
    try {
      e.destroy();
    } catch (_) {
    }
    engines.delete(v);
  }
  try {
    v.pause();
  } catch (_) {
  }
  v.removeAttribute("src");
  try {
    v.load();
  } catch (_) {
  }
}
function kindOf(url) {
  const p = url.split("?")[0].split("#")[0].toLowerCase();
  const m = p.match(/\.([a-z0-9]{2,5})$/);
  const x = m ? m[1] : "";
  if (x === "m3u8" || x === "m3u") return "hls";
  if (x === "ts") return "ts";
  if (["mp4", "mkv", "webm", "mov", "m4v", "avi", "mp3", "aac", "ogg", "flv", "wmv"].includes(x)) return "native";
  return "";
}
function probe(url) {
  return __async(this, null, function* () {
    try {
      const ctl = new AbortController();
      const tm = setTimeout(() => ctl.abort(), 12e3);
      const r = yield fetch(px(url), { signal: ctl.signal });
      const ct = r.headers.get("content-type") || "";
      const rd = r.body.getReader();
      const { value } = yield rd.read();
      clearTimeout(tm);
      ctl.abort();
      if (value && value.length) {
        const h = new TextDecoder().decode(value.slice(0, 32)).replace(/^﻿/, "").trimStart();
        if (h.startsWith("#EXTM3U")) return "hls";
        if (value[0] === 71) return "ts";
      }
      if (/mpegurl/i.test(ct)) return "hls";
      if (/mp2t/i.test(ct)) return "ts";
      if (/video|audio|matroska|octet/i.test(ct)) return "native";
      return "ts";
    } catch (e) {
      return "ts";
    }
  });
}
function playStream(_0, _1) {
  return __async(this, arguments, function* (v, url, o = {}) {
    stopVideo(v);
    const tok = v._tok;
    const fail = (m) => {
      if (v._tok !== tok) return;
      if (WEBOS && !o.native && url[0] !== "/") {
        o.native = true;
        const e = engines.get(v);
        if (e) {
          try {
            e.destroy();
          } catch (_) {
          }
          engines.delete(v);
        }
        v.src = url;
        const pl2 = v.play();
        pl2 && pl2.catch && pl2.catch(() => {
        });
        return;
      }
      if (o.onErr) o.onErr(m);
    };
    const local = url[0] === "/";
    let kind = kindOf(url);
    if (!kind) kind = local ? "native" : yield probe(url);
    if (v._tok !== tok) return;
    const src = local ? url : px(url), abs = new URL(src, location.href).href;
    if (kind === "hls" && window.Hls && Hls.isSupported()) {
      const h = new Hls({ enableWorker: true, maxBufferLength: 30, backBufferLength: 30, manifestLoadingMaxRetry: 3, levelLoadingMaxRetry: 4, fragLoadingMaxRetry: 6 });
      let netTries = 0, medTries = 0;
      h.on(Hls.Events.ERROR, (e, d) => {
        if (!d.fatal) return;
        if (d.type === Hls.ErrorTypes.NETWORK_ERROR && netTries++ < 3 && d.details !== "manifestLoadError") {
          h.startLoad();
          return;
        }
        if (d.type === Hls.ErrorTypes.MEDIA_ERROR && medTries++ < 2) {
          h.recoverMediaError();
          return;
        }
        fail(d.type === Hls.ErrorTypes.MEDIA_ERROR ? "Formato de vídeo/áudio não suportado pelo navegador." : "Não foi possível abrir: canal fora do ar, lista expirada ou limite de conexões do provedor.");
      });
      h.loadSource(abs);
      h.attachMedia(v);
      engines.set(v, { destroy: () => h.destroy(), hls: h });
    } else if (kind === "ts" && window.mpegts && mpegts.getFeatureList().mseLivePlayback) {
      let tries = 0;
      const start = () => {
        if (v._tok !== tok) return;
        const p = mpegts.createPlayer({ type: "mpegts", isLive: !!o.live, url: abs }, { enableWorker: true, lazyLoad: false, liveBufferLatencyChasing: false, autoCleanupSourceBuffer: true });
        p.attachMediaElement(v);
        p.load();
        const pl2 = p.play();
        pl2 && pl2.catch && pl2.catch(() => {
        });
        p.on(mpegts.Events.ERROR, (type, detail) => {
          try {
            p.destroy();
          } catch (_) {
          }
          if (type === mpegts.ErrorTypes.MEDIA_ERROR) return fail("Formato de vídeo/áudio não suportado pelo navegador.");
          if (tries++ < 2 && v._tok === tok) {
            vmsg(o.which || "live", "Reconectando…");
            setTimeout(start, 1500);
          } else fail("Não foi possível abrir: canal fora do ar, lista expirada ou limite de conexões do provedor.");
        });
        engines.set(v, { destroy: () => {
          try {
            p.pause();
            p.unload();
            p.detachMediaElement();
          } catch (_) {
          }
          p.destroy();
        } });
      };
      start();
      return;
    } else {
      v.src = src;
    }
    const pl = v.play();
    pl && pl.catch && pl.catch(() => {
    });
  });
}
function wireVideo(v, which) {
  v.addEventListener("waiting", () => {
    if (v._hasSrc !== false) vmsg(which, "Carregando…");
  });
  v.addEventListener("playing", () => vmsg(which, ""));
  v.addEventListener("canplay", () => {
    if (!v.paused) vmsg(which, "");
  });
  v.addEventListener("error", () => {
    const c = v.error && v.error.code;
    if (!c || !v.getAttribute("src")) return;
    vmsg(which, c === 4 ? "Formato não suportado pelo navegador ou link indisponível." : "Erro ao reproduzir (código " + c + ").");
  });
}
function xctx(s) {
  let b = (s.server || "").trim().replace(/\/+$/, "");
  if (!/^https?:\/\//i.test(b)) b = "http://" + b;
  return { base: b, u: s.user, p: s.pass };
}
function extinf(l) {
  let q = false, i = -1;
  for (let j = 0; j < l.length; j++) {
    const c = l[j];
    if (c === '"') q = !q;
    else if (c === "," && !q) {
      i = j;
      break;
    }
  }
  const head = i < 0 ? l : l.slice(0, i), name = i < 0 ? "" : l.slice(i + 1).trim(), attrs = {};
  head.replace(/([\w-]+)\s*=\s*"([^"]*)"/g, (_, k, v) => {
    attrs[k.toLowerCase()] = v;
  });
  return { name: name || attrs["tvg-name"] || "", attrs };
}
function parseM3U(text, sid) {
  const lines = text.split(/\r?\n/);
  const em = (lines[0] || "").match(/(?:x-tvg-url|url-tvg)\s*=\s*"([^"]+)"/i);
  const live = [], movie = [], smap = /* @__PURE__ */ new Map(), cats = { live: /* @__PURE__ */ new Map(), movie: /* @__PURE__ */ new Map(), series: /* @__PURE__ */ new Map() };
  const addCat = (t, g) => {
    if (!cats[t].has(g)) cats[t].set(g, { id: g, name: g });
  };
  let meta = null, n = 0;
  for (const raw of lines) {
    const l = raw.trim();
    if (!l) continue;
    if (l.startsWith("#EXTINF")) {
      meta = extinf(l);
      continue;
    }
    if (l.startsWith("#EXTGRP:")) {
      if (meta && !meta.attrs["group-title"]) meta.attrs["group-title"] = l.slice(8).trim();
      continue;
    }
    if (l[0] === "#") continue;
    const m = meta || { name: decodeURIComponent(l.split("?")[0].split("/").pop() || "Sem nome"), attrs: {} };
    meta = null;
    const url = l, group = (m.attrs["group-title"] || "").trim() || "Sem categoria", name = m.name || "Sem nome", logo = m.attrs["tvg-logo"] || "";
    const path = url.split("?")[0].toLowerCase(), isFile = /\.(mp4|mkv|avi|mov|wmv|m4v|webm|flv)$/.test(path);
    const se = name.match(/^(.*?)[\s._\-|]*\bS(\d{1,2})\s*E(\d{1,3})\b(.*)$/i);
    if (path.includes("/series/") || se && (isFile || path.includes("/movie/"))) {
      const sname = (se ? se[1] : name).replace(/[\s\-–|:.]+$/, "").trim() || name, key = group + "|" + sname.toLowerCase();
      let s = smap.get(key);
      if (!s) {
        s = { k: sid + "|s|" + key, name: sname, logo, group, eps: [] };
        smap.set(key, s);
        addCat("series", group);
      }
      if (!s.logo && logo) s.logo = logo;
      s.eps.push({ s: se ? +se[2] : 1, e: se ? +se[3] : s.eps.length + 1, title: se && se[4].replace(/^[\s\-–:|.]+/, "").trim() || (se ? "Episódio " + +se[3] : name), url, img: logo });
    } else if (path.includes("/movie/") || isFile) {
      movie.push({ k: sid + "|m|" + url, name, logo, group, url });
      addCat("movie", group);
    } else {
      live.push({ k: sid + "|l|" + url, name, logo, group, url, epgId: m.attrs["tvg-id"] || "", tvgName: m.attrs["tvg-name"] || "", num: m.attrs["tvg-chno"] || ++n });
      addCat("live", group);
    }
  }
  const series = [...smap.values()];
  series.forEach((s) => s.eps.sort((a, b) => a.s - b.s || a.e - b.e));
  return { live, movie, series, cats: { live: [...cats.live.values()], movie: [...cats.movie.values()], series: [...cats.series.values()] }, epg: em ? em[1].split(",")[0].trim() : null };
}
function loadM3U(src) {
  return __async(this, null, function* () {
    const text = src.file ? yield idb.get("file:" + src.id) : yield txt(src.url);
    if (!text || !/^\s*﻿?#EXTM3U/.test(text) && !text.includes("#EXTINF")) throw new Error("o conteúdo recebido não é uma lista M3U");
    return parseM3U(text, src.id);
  });
}
function srvOff(si) {
  try {
    const m = String(si.time_now || "").match(/(\d{4})-(\d\d)-(\d\d) (\d\d):(\d\d):(\d\d)/);
    if (!m || !si.timestamp_now) return 0;
    const loc = Date.UTC(+m[1], +m[2] - 1, +m[3], +m[4], +m[5], +m[6]) / 1e3;
    return Math.round((loc - +si.timestamp_now) / 900) * 900;
  } catch (e) {
    return 0;
  }
}
function loadXtream(src) {
  return __async(this, null, function* () {
    const x = xctx(src), auth = `username=${enc(x.u)}&password=${enc(x.p)}`;
    const api = (a) => txt(`${x.base}/player_api.php?${auth}${a ? "&action=" + a : ""}`).then((t) => {
      try {
        return JSON.parse(t);
      } catch (e) {
        throw new Error("resposta inválida do servidor");
      }
    });
    const info = yield api("");
    if (!info || !info.user_info) throw new Error("o servidor não respondeu como Xtream Codes");
    if (String(info.user_info.auth) === "0") throw new Error("usuário ou senha inválidos");
    const ui = info.user_info, fm = arr(ui.allowed_output_formats), ext = S.cfg.fmt !== "auto" ? S.cfg.fmt : fm.includes("m3u8") ? "m3u8" : "ts";
    status("Baixando canais, filmes e séries…", true);
    const [lc, ls, vc, vs, sc, ss] = (yield Promise.all(["get_live_categories", "get_live_streams", "get_vod_categories", "get_vod_streams", "get_series_categories", "get_series"].map((a) => api(a).catch(() => [])))).map(arr);
    const sid = src.id, B = x.base, U = enc(x.u), P = enc(x.p), cat = (a) => a.map((c) => ({ id: String(c.category_id), name: c.category_name || "Sem nome" }));
    const live = ls.map((s, i) => {
      var _a;
      return { k: sid + "|l|" + s.stream_id, name: s.name || "", logo: s.stream_icon || "", group: String((_a = s.category_id) != null ? _a : ""), xid: s.stream_id, epgId: s.epg_channel_id || "", num: s.num || i + 1, arch: +s.tv_archive ? +s.tv_archive_duration || 1 : 0, url: `${B}/live/${U}/${P}/${s.stream_id}.${ext}` };
    });
    const movie = vs.map((s) => {
      var _a;
      return { k: sid + "|m|" + s.stream_id, name: s.name || "", logo: s.stream_icon || "", group: String((_a = s.category_id) != null ? _a : ""), xid: s.stream_id, rating: s.rating || "", url: `${B}/movie/${U}/${P}/${s.stream_id}.${s.container_extension || "mp4"}` };
    });
    const series = ss.map((s) => {
      var _a;
      return { k: sid + "|s|" + s.series_id, name: s.name || "", logo: s.cover || "", group: String((_a = s.category_id) != null ? _a : ""), xid: s.series_id, rating: s.rating || "", plot: s.plot || "", year: String(s.releaseDate || s.release_date || "").slice(0, 4) };
    });
    return { live, movie, series, cats: { live: cat(lc), movie: cat(vc), series: cat(sc) }, acct: { status: ui.status, exp: +ui.exp_date || 0, max: ui.max_connections, active: ui.active_cons, fmt: ext, tzOff: srvOff(info.server_info) }, epg: `${x.base}/xmltv.php?${auth}` };
  });
}
function loadActive(force) {
  return __async(this, null, function* () {
    const src = S.sources.find((s) => s.id === S.active) || S.sources[0] || null;
    stopVideo($("#liveVideo"));
    vmsg("live", "");
    mvStop();
    Object.assign(S, { src, liveOn: false, epg: null, cur: null, acct: null, x: null, items: { live: [], movie: [], series: [] }, cat: { live: [], movie: [], series: [] }, sel: { live: "*", movie: "*", series: "*" }, guideCat: null });
    S.epgLoad++;
    if (!src) {
      $("#empty").classList.add("on");
      status("");
      renderAll();
      return;
    }
    $("#empty").classList.remove("on");
    S.active = src.id;
    LS.set("active", src.id);
    if (src.type === "xtream") S.x = xctx(src);
    let cached = null;
    try {
      cached = yield idb.get("cat:" + src.id);
    } catch (e) {
    }
    let data = !force && cached && Date.now() - cached.at < 12 * 36e5 ? cached : null;
    if (!data) {
      status("Carregando " + src.name + "…", true);
      try {
        data = src.type === "xtream" ? yield loadXtream(src) : yield loadM3U(src);
        data.at = Date.now();
        idb.set("cat:" + src.id, data).catch((e) => console.warn(e));
      } catch (e) {
        if (cached) {
          data = cached;
          toast("Não consegui atualizar a lista (" + e.message + "). Usando a cópia salva.", true);
        } else {
          status("");
          toast("Erro ao carregar a lista: " + e.message, true);
          data = { live: [], movie: [], series: [], cats: { live: [], movie: [], series: [] } };
        }
      }
    }
    if (S.src !== src) return;
    S.items = { live: data.live || [], movie: data.movie || [], series: data.series || [] };
    S.cat = data.cats || S.cat;
    S.acct = data.acct || null;
    S.epgHint = data.epg || null;
    status(`${S.items.live.length.toLocaleString("pt-BR")} canais · ${S.items.movie.length.toLocaleString("pt-BR")} filmes · ${S.items.series.length.toLocaleString("pt-BR")} séries`);
    renderAll();
    loadEPG(src, false);
  });
}
const ENT = { amp: "&", lt: "<", gt: ">", quot: '"', apos: "'" };
const unent = (t) => t.replace(/&(#x?[0-9a-f]+|\w+);/gi, (m, c) => c[0] === "#" ? String.fromCharCode(c[1] === "x" || c[1] === "X" ? parseInt(c.slice(2), 16) : +c.slice(1)) : ENT[c.toLowerCase()] || m);
function xtTime(s) {
  s = String(s || "").trim();
  const t = Date.UTC(+s.slice(0, 4), +s.slice(4, 6) - 1, +s.slice(6, 8), +s.slice(8, 10), +s.slice(10, 12), +s.slice(12, 14) || 0) / 1e3;
  const m = s.slice(14).trim().match(/^([+-])(\d\d)(\d\d)/);
  if (!m) return t;
  const off = +m[2] * 3600 + +m[3] * 60;
  return m[1] === "+" ? t - off : t + off;
}
function epgLocal(url, force) {
  return __async(this, null, function* () {
    const key = "epg:" + url;
    let c = null;
    try {
      c = yield idb.get(key);
    } catch (e) {
    }
    if (!force && c && Date.now() - c.at < 4 * 36e5) return c.data;
    let r;
    try {
      r = yield fetch(url, { cache: "no-store" });
    } catch (e) {
      if (c) return c.data;
      throw e;
    }
    if (!r.ok) {
      if (c) return c.data;
      throw new Error("HTTP " + r.status);
    }
    const now = Date.now() / 1e3, lo = now - 7200, hi = now + 72e3, names = {}, progs = {};
    const dec = new TextDecoder("utf-8");
    let buf = "", inf = null, first = true;
    const attrs = (h) => {
      const a = {};
      h.replace(/([\w-]+)\s*=\s*"([^"]*)"/g, (_, k, v) => {
        a[k] = v;
      });
      return a;
    };
    const tag = (b, n) => {
      const m = b.match(new RegExp("<" + n + "[^>]*>([\\s\\S]*?)</" + n + ">"));
      return m ? unent(m[1].replace(/<!\[CDATA\[|\]\]>/g, "")).trim() : "";
    };
    const putName = (raw, id) => {
      const k = norm(raw);
      if (k && !(k in names)) names[k] = id;
    };
    const eat = () => {
      let i = 0;
      for (; ; ) {
        const a = buf.indexOf("<channel", i), b = buf.indexOf("<programme", i);
        if (a < 0 && b < 0) {
          i = Math.max(i, buf.length - 20);
          break;
        }
        const isP = b >= 0 && (a < 0 || b < a), st = isP ? b : a, endTag = isP ? "</programme>" : "</channel>";
        let e = buf.indexOf(endTag, st), gt = buf.indexOf(">", st);
        if (gt < 0) break;
        let el;
        if (buf[gt - 1] === "/") {
          el = buf.slice(st, gt + 1);
          i = gt + 1;
        } else {
          if (e < 0) {
            i = st;
            break;
          }
          el = buf.slice(st, e + endTag.length);
          i = e + endTag.length;
        }
        const at = attrs(el.slice(0, el.indexOf(">")));
        if (!isP) {
          const id = at.id;
          if (id) {
            putName(id, id);
            el.replace(/<display-name[^>]*>([\s\S]*?)<\/display-name>/g, (_, n) => {
              putName(unent(n), id);
            });
          }
        } else {
          let s0, e0;
          try {
            s0 = xtTime(at.start);
            e0 = at.stop ? xtTime(at.stop) : s0 + 3600;
          } catch (x) {
            continue;
          }
          if (at.channel && s0 && e0 >= lo && s0 <= hi) {
            let d = tag(el, "desc");
            if (d.length > 180) d = d.slice(0, 177).trim() + "...";
            (progs[at.channel] || (progs[at.channel] = [])).push([s0, e0, tag(el, "title"), d]);
          }
        }
      }
      buf = buf.slice(i);
    };
    const push = (chunk) => {
      buf += dec.decode(chunk, { stream: true });
      if (buf.length > 65536) eat();
    };
    const rd = r.body.getReader();
    for (; ; ) {
      const { done, value } = yield rd.read();
      if (done) break;
      if (first) {
        first = false;
        if (value[0] === 31 && value[1] === 139) {
          if (!window.pako) throw new Error("guia compactado sem suporte");
          inf = new pako.Inflate();
          inf.onData = push;
        }
      }
      if (inf) inf.push(value, false);
      else push(value);
    }
    if (inf) inf.push(new Uint8Array(0), true);
    buf += dec.decode();
    eat();
    for (const k in progs) progs[k].sort((a, b) => a[0] - b[0]);
    const data = { gerado: Math.floor(now), progs, names };
    idb.set(key, { at: Date.now(), data }).catch(() => {
    });
    return data;
  });
}
function loadEPG(src, force) {
  return __async(this, null, function* () {
    const u = (src.epg || "").trim() || S.epgHint;
    if (!u) return;
    const tok = ++S.epgLoad;
    const before = $("#status").textContent;
    status("Carregando guia de programação…", true);
    try {
      let j;
      if (WEBOS) j = yield epgLocal(u, force);
      else {
        const r = yield fetch("/epg?u=" + enc(u) + uaQ() + (force ? "&force=1" : ""));
        j = yield r.json();
        if (!r.ok) throw new Error(j.erro || "HTTP " + r.status);
      }
      if (tok !== S.epgLoad) return;
      S.epg = j;
      S.epgTok++;
      status(before + " · guia: " + Object.keys(j.progs || {}).length.toLocaleString("pt-BR") + " canais");
      refreshNow();
      renderLiveInfo();
      if (S.view === "guide") renderGuide();
    } catch (e) {
      if (tok === S.epgLoad) status(before + " · guia indisponível");
      console.warn("EPG", e);
    }
  });
}
function epgOf(it) {
  if (it._et === S.epgTok && it._ep !== void 0) return it._ep;
  let r = null;
  const E = S.epg;
  if (E && E.progs) {
    let id = it.epgId && E.progs[it.epgId] ? it.epgId : null;
    if (!id) for (const c of [it.epgId, it.tvgName, it.name]) {
      const n = c && E.names[norm(c)];
      if (n && E.progs[n]) {
        id = n;
        break;
      }
    }
    if (id) r = E.progs[id];
  }
  if (!r && it._short) r = it._short;
  it._ep = r;
  it._et = S.epgTok;
  return r;
}
function nowProg(it) {
  const a = epgOf(it);
  if (!a) return null;
  const t = nowS();
  return a.find((p) => p[0] <= t && t < p[1]) || null;
}
function shortEpg(it) {
  return __async(this, null, function* () {
    if (!S.x || !it.xid || it._short) return;
    try {
      const j = JSON.parse(yield txt(xapi("get_short_epg", "&stream_id=" + it.xid + "&limit=16")));
      const b64 = (s) => {
        try {
          return new TextDecoder().decode(Uint8Array.from(atob(s || ""), (c) => c.charCodeAt(0)));
        } catch (e) {
          return s || "";
        }
      };
      const ts = (s) => Date.parse(String(s).replace(" ", "T")) / 1e3;
      const a = arr(j.epg_listings).map((e) => [+e.start_timestamp || ts(e.start), +e.stop_timestamp || ts(e.end || e.stop), b64(e.title), b64(e.description)]).filter((p) => p[0] && p[1]).sort((a2, b) => a2[0] - b[0]);
      if (a.length) {
        it._short = a;
        it._ep = void 0;
        if (S.cur === it) renderLiveInfo();
        refreshNow();
      }
    } catch (e) {
    }
  });
}
const FW = ["f", "b"];
const favName = (w) => (w === "f" ? S.cfg.favF : S.cfg.favB) || (w === "f" ? "Fran" : "Berga");
const favL = (w) => favName(w).trim().charAt(0).toUpperCase() || w.toUpperCase();
function favRoot() {
  const id = S.src && S.src.id;
  if (!id) return null;
  let x = S.favs[id];
  if (!x) x = S.favs[id] = { f: {}, b: {} };
  if (x.live || x.movie || x.series) {
    x = { f: {}, b: { live: x.live || {}, movie: x.movie || {}, series: x.series || {} } };
    S.favs[id] = x;
    LS.set("favs", S.favs);
  }
  return x;
}
function favBucket(t, w) {
  const x = favRoot();
  if (!x) return {};
  const u = x[w || "b"] || (x[w || "b"] = {});
  return u[t] || (u[t] = {});
}
const isFav = (t, it, w) => !!favBucket(t, w)[it.k];
const starBtns = (t, it) => `<span class="stars">${FW.map((w) => `<button class="star${isFav(t, it, w) ? " on" : ""}" data-w="${w}" title="Favoritos ${esc(favName(w))}">★<i>${esc(favL(w))}</i></button>`).join("")}</span>`;
const favBtnTxt = (t, it, w) => `${isFav(t, it, w) ? "★" : "☆"} ${favName(w)}`;
function toggleFav(t, it, w) {
  w = w || "b";
  const b = favBucket(t, w);
  if (b[it.k]) delete b[it.k];
  else b[it.k] = snap(it);
  LS.set("favs", S.favs);
  const on = !!b[it.k];
  document.querySelectorAll(".ch,.card").forEach((h) => {
    if (h._it && h._it.k === it.k) {
      const s = h.querySelector('.star[data-w="' + w + '"]');
      s && s.classList.toggle("on", on);
    }
  });
  renderCats(t);
  if (S.sel[t] === "fav:" + w && S.view === t) renderItems(t);
  if (S.view === "fav") renderFav();
  if (S.cur && S.cur.k === it.k) renderLiveInfo();
  if (S.view === "guide" && S.guideCat === "fav:" + w) renderGuide();
  toast((on ? "Adicionado aos favoritos " : "Removido dos favoritos ") + "d" + (w === "f" ? "a " : "o ") + favName(w));
  return on;
}
function saveProg(force) {
  const v = $("#vodVideo"), V = S.vod;
  if (!V || !v.duration || !isFinite(v.duration)) return;
  const t = v.currentTime, d = v.duration;
  if (t < 20 && !force) return;
  if (d - t < Math.max(60, d * 0.04)) delete S.prog[V.it.k];
  else S.prog[V.it.k] = { t, d, at: Date.now(), it: snap(V.it) };
  const ks = Object.keys(S.prog).sort((a, b) => S.prog[b].at - S.prog[a].at);
  ks.slice(80).forEach((k) => delete S.prog[k]);
  LS.set("prog", S.prog);
}
function visibleCats(t) {
  const c = S.cat[t] || [];
  return S.cfg.hideAdult ? c.filter((x) => !ADULT.test(x.name)) : c;
}
function itemsOf(t) {
  let a = S.items[t];
  if (S.cfg.hideAdult) {
    const bad = new Set((S.cat[t] || []).filter((x) => ADULT.test(x.name)).map((x) => x.id));
    if (bad.size) a = a.filter((i) => !bad.has(i.group));
  }
  const q = norm(S.q);
  if (q) return a.filter((i) => (i._n || (i._n = norm(i.name))).includes(q));
  const s = S.sel[t];
  if (s === "*") return a;
  if (s.slice(0, 4) === "fav:") {
    const b = favBucket(t, s.slice(4));
    return a.filter((i) => b[i.k]);
  }
  return a.filter((i) => i.group === s);
}
function renderCats(t) {
  const el = $("#" + t + "Cats");
  if (!el) return;
  const counts = /* @__PURE__ */ new Map();
  for (const i of S.items[t]) counts.set(i.group, (counts.get(i.group) || 0) + 1);
  const vc = visibleCats(t), tot = vc.length < (S.cat[t] || []).length ? vc.reduce((a, c) => a + (counts.get(c.id) || 0), 0) : S.items[t].length;
  const rows = [{ id: "*", name: S.q ? "Resultados da busca" : "Todos", n: S.q ? itemsOf(t).length : tot }, ...FW.map((w) => ({ id: "fav:" + w, name: "★ " + favName(w), n: Object.keys(favBucket(t, w)).length })), ...vc.map((c) => __spreadProps(__spreadValues({}, c), { n: counts.get(c.id) || 0 })).filter((c) => c.n > 0)];
  el.innerHTML = rows.map((c) => `<div class="cat${(S.q ? c.id === "*" : S.sel[t] === c.id) ? " on" : ""}" tabindex="0" data-id="${esc(c.id)}"><span>${esc(c.name)}</span><span class="n">${c.n.toLocaleString("pt-BR")}</span></div>`).join("");
}
function liveRow(it) {
  const d = document.createElement("div");
  d.className = "ch" + (S.cur && S.cur.k === it.k ? " on" : "");
  d.tabIndex = 0;
  d._it = it;
  d.innerHTML = `<span class="num">${esc(it.num)}</span><img class="chlogo" loading="lazy" ${it.logo ? `src="${esc(it.logo)}"` : ""} alt=""><div class="chtxt"><div class="chname">${esc(it.name)}</div><div class="chnow"></div><div class="bar"><i></i></div></div>${starBtns("live", it)}`;
  updNow(d);
  return d;
}
function updNow(d) {
  const p = nowProg(d._it);
  d.querySelector(".chnow").textContent = p ? p[2] : "";
  const b = d.querySelector(".bar");
  b.style.visibility = p ? "visible" : "hidden";
  if (p) b.firstChild.style.width = pct(p) + "%";
}
function refreshNow() {
  document.querySelectorAll("#liveList .ch,#favBox .ch").forEach(updNow);
}
function card(t, it) {
  const d = document.createElement("div");
  d.className = "card";
  d.tabIndex = 0;
  d._it = it;
  d._t = t;
  const pr = S.prog[it.k];
  const r = parseFloat(it.rating);
  d.innerHTML = `<div class="poster"><div class="ph">${esc(it.name)}</div>${it.logo ? `<img loading="lazy" src="${esc(it.logo)}" alt="">` : ""}${r > 0 ? `<span class="rate">★ ${r.toFixed(1)}</span>` : ""}${t === "cont" ? '<span class="stars"><button class="star" title="Remover de Continuar assistindo">✕</button></span>' : starBtns(t, it)}${pr && pr.d ? `<div class="bar pbar"><i style="width:${Math.min(100, pr.t / pr.d * 100)}%"></i></div>` : ""}</div><div class="ctitle">${esc(it.name)}</div>`;
  return d;
}
function renderItems(t) {
  if (t === "live") {
    const items = itemsOf("live");
    const box = $("#liveList");
    chunked(box, items, liveRow);
    if (!items.length) box.innerHTML = `<p class="muted" style="padding:16px">${S.q ? "Nenhum canal encontrado." : "Nenhum canal nesta categoria."}</p>`;
  } else {
    const items = itemsOf(t);
    const box = $("#" + t + "Grid");
    chunked(box, items, (it) => card(t, it), 90);
    if (!items.length) box.innerHTML = `<p class="muted">${S.q ? "Nada encontrado." : "Nenhum item nesta categoria."}</p>`;
  }
}
function renderLiveInfo() {
  const it = S.cur, box = $("#liveInfo"), ep = $("#liveEpg");
  if (!it) {
    box.innerHTML = `<p class="muted">${S.items.live.length ? "Escolha um canal na lista. Dica: use ↑ ↓ para trocar de canal e F para tela cheia." : ""}</p>`;
    ep.innerHTML = "";
    return;
  }
  const a = epgOf(it) || [], t = nowS(), cur = a.find((p) => p[0] <= t && t < p[1]), nx = a.filter((p) => p[0] >= (cur ? cur[1] : t) - 1).slice(0, 14);
  box.innerHTML = `<div class="niTop"><img ${it.logo ? `src="${esc(it.logo)}"` : ""} alt=""><div class="grow"><div class="niName">${esc(it.name)}</div>${cur ? `<div class="niProg">${esc(cur[2])}</div><div class="niTime">${hhmm(cur[0])} – ${hhmm(cur[1])} · termina em ${Math.max(1, Math.round((cur[1] - t) / 60))} min</div><div class="bar big"><i style="width:${pct(cur)}%"></i></div>` : `<div class="niTime">${S.epg || it._short ? "Sem programação para este canal" : "Guia de programação não carregado"}</div>`}</div><span class="stars" style="font-size:24px">${FW.map((w) => `<button class="star${isFav("live", it, w) ? " on" : ""}" data-a="fav" data-w="${w}" title="Favoritos ${esc(favName(w))}" style="font-size:26px">★<i>${esc(favL(w))}</i></button>`).join("")}</span><button class="btn sm" data-a="golive" title="Pular para o momento atual da transmissão (resolve travadas)">⟳ Ao vivo</button>${S.x && it.arch ? '<button class="btn sm" data-a="arch" title="Assistir programas que já passaram">⏪ Anteriores</button>' : ""}<button class="btn sm" data-a="pip" title="Assistir numa janela flutuante por cima de qualquer programa">⧉ Flutuante</button><button class="btn sm" data-a="fs">⛶ Tela cheia</button></div>${cur && cur[3] ? `<p class="desc">${esc(cur[3])}</p>` : ""}`;
  ep.innerHTML = nx.length ? "<h4>A seguir</h4>" + nx.map((p) => `<div class="ep${recMark(it, p) ? " rec" : ""}" tabindex="0" data-s="${p[0]}"><span class="t">${hhmm(p[0])}</span><span>${esc(p[2])}</span></div>`).join("") : "";
}
function renderGuide() {
  const sel = $("#guideCat"), cats = visibleCats("live");
  if (!S.guideCat) S.guideCat = S.sel.live !== "*" && S.sel.live.slice(0, 4) !== "fav:" ? S.sel.live : Object.keys(favBucket("live", "b")).length ? "fav:b" : Object.keys(favBucket("live", "f")).length ? "fav:f" : cats[0] && cats[0].id || "fav:b";
  sel.innerHTML = FW.map((w) => `<option value="fav:${w}">★ ${esc(favName(w))}</option>`).join("") + cats.map((c) => `<option value="${esc(c.id)}">${esc(c.name)}</option>`).join("");
  sel.value = S.guideCat;
  let chs = S.guideCat.slice(0, 4) === "fav:" ? S.items.live.filter((i) => isFav("live", i, S.guideCat.slice(4))) : S.items.live.filter((i) => i.group === S.guideCat);
  const total = chs.length;
  chs = chs.slice(0, 250);
  $("#guideNote").textContent = (S.epg ? "" : "Guia de programação ainda não carregado. ") + (total > 250 ? `Mostrando 250 de ${total} canais.` : "");
  const PX = 5, GN = matchMedia("(max-width:900px)").matches ? 120 : 210, nt = nowS(), t0 = Math.floor((nt - 1800) / 1800) * 1800, t1 = t0 + 8 * 3600, W = (t1 - t0) / 60 * PX;
  let h = `<div class="gInner" style="width:${GN + W}px"><div class="gHead"><div class="gCorner">${total} ${total === 1 ? "canal" : "canais"}</div><div class="gRuler" style="width:${W}px">`;
  for (let t = t0; t < t1; t += 1800) h += `<span style="left:${(t - t0) / 60 * PX}px">${hhmm(t)}</span>`;
  h += "</div></div>";
  chs.forEach((it, ri) => {
    const a = (epgOf(it) || []).filter((p) => p[1] > t0 && p[0] < t1);
    h += `<div class="gRow" data-i="${ri}"><div class="gName" tabindex="0"><img ${it.logo ? `src="${esc(it.logo)}"` : ""} alt="" loading="lazy"><span>${esc(it.name)}</span></div><div class="gTrack" style="width:${W}px">`;
    if (!a.length) h += `<div class="gProg empty" style="left:4px;width:${W - 8}px">Sem informação de programação</div>`;
    for (const p of a) {
      const l = Math.max(0, (p[0] - t0) / 60 * PX), r = Math.min(W, (p[1] - t0) / 60 * PX), cls = (p[0] <= nt && nt < p[1] ? " live" : "") + (p[1] <= nt && S.x && it.arch ? " cu" : "") + (recMark(it, p) ? " rec" : "");
      h += `<div class="gProg${cls}" tabindex="0" data-s="${p[0]}" style="left:${l + 1}px;width:${Math.max(0, r - l - 3)}px" title="${esc(hhmm(p[0]) + " – " + hhmm(p[1]) + "  " + p[2] + (p[3] ? "\n\n" + p[3] : ""))}"><b>${esc(p[2])}</b><small>${hhmm(p[0])} – ${hhmm(p[1])}</small></div>`;
    }
    h += "</div></div>";
  });
  if (!chs.length) h += `<p class="muted" style="padding:16px">Nenhum canal aqui.</p>`;
  h += `<div class="gNow" style="left:${GN + (nt - t0) / 60 * PX}px"></div></div>`;
  const g = $("#guide");
  g.innerHTML = h;
  g._chs = chs;
  g.scrollLeft = Math.max(0, (nt - t0) / 60 * PX - 140);
}
function renderFav() {
  const box = $("#favBox");
  box.innerHTML = "";
  const sid = S.src ? S.src.id : "~", q = norm(S.q), f = (a) => q ? a.filter((i) => norm(i.name).includes(q)) : a;
  const cont = f(Object.values(S.prog).filter((p) => p.it && String(p.it.k).includes(sid)).sort((a, b) => b.at - a.at).map((p) => p.it));
  const sec = (title, items, make, cls) => {
    if (!items.length) return;
    const h = document.createElement("h3");
    h.textContent = title;
    box.appendChild(h);
    const g = document.createElement("div");
    g.className = cls;
    items.forEach((i) => g.appendChild(make(i)));
    box.appendChild(g);
  };
  const w = S.favTab === "f" ? "f" : "b", tabs = document.createElement("div");
  tabs.className = "favTabs";
  tabs.innerHTML = FW.map((x) => `<button class="btn${x === w ? " pri" : ""}" data-ft="${x}">★ Favoritos ${esc(favName(x))}</button>`).join("");
  box.appendChild(tabs);
  sec("Continuar assistindo", cont, (it) => {
    const c = card("cont", it);
    return c;
  }, "grid");
  const n0 = box.children.length;
  sec("Canais", f(Object.values(favBucket("live", w))), liveRow, "chips");
  sec("Filmes", f(Object.values(favBucket("movie", w))), (it) => card("movie", it), "grid");
  sec("Séries", f(Object.values(favBucket("series", w))), (it) => card("series", it), "grid");
  if (box.children.length === n0) {
    const p = document.createElement("p");
    p.className = "muted";
    p.style.marginTop = "16px";
    p.innerHTML = `Nada nos favoritos d${w === "f" ? "a" : "o"} ${esc(favName(w))} ainda. Toque na estrela com <b>${esc(favL(w))}</b> de um canal, filme ou série.`;
    box.appendChild(p);
  }
}
function renderAll() {
  ["live", "movie", "series"].forEach((t) => {
    renderCats(t);
    renderItems(t);
  });
  renderLiveInfo();
  if (S.view === "guide") renderGuide();
  if (S.view === "fav") renderFav();
  if (S.view === "multi") mvStart();
  placePlayer();
}
function setView(v) {
  const prev = S.view;
  S.view = v;
  LS.set("view", v);
  document.querySelectorAll("#nav button").forEach((b) => b.classList.toggle("on", b.dataset.view === v));
  document.querySelectorAll(".view").forEach((s) => s.classList.toggle("on", s.id === "v-" + v));
  if (prev === "multi" && v !== "multi") mvStop();
  syncLive();
  if (v === "guide") renderGuide();
  if (v === "fav") renderFav();
  if (v === "multi") mvStart();
  if (v === "dl") {
    renderDl(true);
    dlFetch();
  }
  if (v === "rec") {
    renderRec(true);
    recFetch();
  }
}
const vodOpen = () => !$("#vodPlayer").classList.contains("hidden");
function placePlayer() {
  const w = $("#liveWrap"), pane = $("#livePane"), slot = $("#miniSlot");
  const show = !!(S.liveOn && S.cur && !vodOpen() && !S.nativeOpen && !S.appPaused && S.view !== "live" && S.view !== "multi");
  if (show) {
    if (w.parentNode !== slot) slot.appendChild(w);
    $("#miniName").textContent = S.cur.name;
  } else if (w.parentNode !== pane) pane.insertBefore(w, pane.firstChild);
  $("#mini").classList.toggle("on", show);
}
function syncLive() {
  const v = $("#liveVideo"), blocked = vodOpen() || S.view === "multi" || S.nativeOpen || S.appPaused;
  if (S.liveOn && S.cur && !blocked) {
    if (v._k !== S.cur.k) startLive(S.cur);
  } else if (v._k) {
    stopVideo(v);
    vmsg("live", "");
  }
  placePlayer();
}
function startLive(it) {
  const v = $("#liveVideo");
  vmsg("live", "Carregando…");
  playStream(v, it.url, { live: true, which: "live", onErr: (m) => {
    if (AND && S.cur === it && /Formato/.test(m)) {
      vmsg("live", "Este canal precisa do player do Android. Abrindo…");
      setTimeout(() => {
        if (S.cur === it && !S.nativeOpen) liveFull();
      }, 900);
    } else vmsg("live", m);
  } });
  v._k = it.k;
  if (S.x && !epgOf(it)) shortEpg(it);
}
function pip() {
  if (AND) return liveFull(true);
  const v = $("#liveVideo");
  if (document.pictureInPictureElement) return document.exitPictureInPicture().catch(() => {
  });
  if (!v.requestPictureInPicture) return toast("Seu navegador não suporta janela flutuante (Picture-in-Picture).", true);
  v.requestPictureInPicture().catch(() => toast("Aguarde o canal começar a tocar e tente de novo.", true));
}
(function miniDrag() {
  const m = $("#mini"), bar = $("#miniBar");
  let sx, sy, ox, oy, drag = false;
  const pos = LS.get("miniPos", null);
  const apply = (x, y) => {
    x = Math.max(0, Math.min(innerWidth - m.offsetWidth, x));
    y = Math.max(0, Math.min(innerHeight - 60, y));
    m.style.left = x + "px";
    m.style.top = y + "px";
    m.style.right = "auto";
    m.style.bottom = "auto";
  };
  if (pos) requestAnimationFrame(() => {
    m.style.width = (pos.w || 400) + "px";
    if (pos.x != null) apply(pos.x, pos.y);
  });
  bar.addEventListener("pointerdown", (e) => {
    if (e.target.closest("button")) return;
    drag = true;
    bar.setPointerCapture(e.pointerId);
    const r = m.getBoundingClientRect();
    sx = e.clientX;
    sy = e.clientY;
    ox = r.left;
    oy = r.top;
  });
  bar.addEventListener("pointermove", (e) => {
    if (drag) apply(ox + e.clientX - sx, oy + e.clientY - sy);
  });
  const save = () => {
    const r = m.getBoundingClientRect();
    LS.set("miniPos", { x: m.style.left ? r.left : null, y: m.style.top ? r.top : null, w: r.width });
  };
  bar.addEventListener("pointerup", () => {
    if (drag) {
      drag = false;
      save();
    }
  });
  new ResizeObserver(() => {
    if (m.classList.contains("on")) save();
  }).observe(m);
  bar.onclick = (e) => {
    const b = e.target.closest("[data-m]");
    if (!b) return;
    const a = b.dataset.m;
    if (a === "live") goLive();
    else if (a === "back") setView("live");
    else if (a === "pip") pip();
    else {
      S.liveOn = false;
      if (document.pictureInPictureElement) document.exitPictureInPicture().catch(() => {
      });
      syncLive();
    }
  };
})();
const MV = { layout: LS.get("mvLayout", "4"), aud: 0, built: false };
function mvSlots() {
  const id = S.src ? S.src.id : "~";
  return S.mvAll[id] || (S.mvAll[id] = [null, null, null, null]);
}
function mvItem(i) {
  const k = mvSlots()[i];
  return k ? S.items.live.find((x) => x.k === k) || null : null;
}
function mvBuild() {
  const g = $("#mvGrid");
  g.className = "mvGrid" + (MV.layout === "13" ? " l13" : "");
  document.querySelectorAll("#v-multi [data-l]").forEach((b) => b.classList.toggle("pri", b.dataset.l === MV.layout));
  if (MV.built) return;
  MV.built = true;
  g.innerHTML = [0, 1, 2, 3].map((i) => `<div class="mvCell" tabindex="0" data-i="${i}"><video id="mv${i}" playsinline muted></video><div class="vmsg" id="mv${i}Msg"></div><div class="mvAdd"><div><b>+</b>Escolher canal</div></div><div class="mvLbl"><span></span><button data-x="swap" title="Trocar canal">⇄ Trocar</button><button data-x="fs" title="Tela cheia">⛶</button><button data-x="rm" title="Remover">✕</button></div><div class="mvAud">🔊 som</div></div>`).join("");
  for (let i = 0; i < 4; i++) wireVideo($("#mv" + i), "mv" + i);
}
function mvRender() {
  mvBuild();
  for (let i = 0; i < 4; i++) {
    const c = $(`.mvCell[data-i="${i}"]`), it = mvItem(i);
    c.querySelector(".mvAdd").style.display = it ? "none" : "grid";
    c.querySelector(".mvLbl").style.display = it ? "flex" : "none";
    c.querySelector(".mvLbl span").textContent = it ? it.name : "";
    c.classList.toggle("aud", !!it && MV.aud === i);
  }
}
function mvAudio() {
  for (let i = 0; i < 4; i++) {
    const v = $("#mv" + i);
    if (v) v.muted = i !== MV.aud;
  }
  mvRender();
}
function mvPlay(i, it) {
  const v = $("#mv" + i);
  vmsg("mv" + i, "Carregando…");
  playStream(v, it.url, { live: true, which: "mv" + i, onErr: (m) => vmsg("mv" + i, m) });
  v._k = it.k;
}
function mvStart() {
  if (S.nativeOpen || S.appPaused) return;
  mvRender();
  if (!mvItem(MV.aud)) {
    const f = [0, 1, 2, 3].find((i) => mvItem(i));
    MV.aud = f === void 0 ? 0 : f;
  }
  mvAudio();
  let d = 0;
  for (let i = 0; i < 4; i++) {
    const it = mvItem(i), v = $("#mv" + i);
    if (it && v._k !== it.k) {
      v._k = it.k;
      const w = d;
      d += 400;
      setTimeout(() => {
        if (S.view === "multi" && mvItem(i) === it) mvPlay(i, it);
      }, w);
    } else if (!it && v._k) {
      stopVideo(v);
      vmsg("mv" + i, "");
    }
  }
  const n = mvSlots().filter(Boolean).length, mx = S.acct ? +S.acct.max : 0;
  if (mx && n > mx) toast(`Seu plano permite ${mx} ${mx === 1 ? "conexão" : "conexões"} ao mesmo tempo. Com ${n} canais abertos, alguns podem não carregar.`, true);
}
function mvStop() {
  for (let i = 0; i < 4; i++) {
    const v = document.getElementById("mv" + i);
    if (v && v._k) {
      stopVideo(v);
      vmsg("mv" + i, "");
    }
  }
}
function mvPick(i) {
  S.modalFor = "mvpick";
  const cats = visibleCats("live");
  modal(`<button class="mx" data-close>✕</button><h2>Escolher canal · quadro ${i + 1}</h2><div class="row2" style="margin:14px 0 10px"><input id="pkQ" class="pkIn" placeholder="Buscar canal…" autocomplete="off"><select id="pkCat" class="pkIn"><option value="*">Todas as categorias</option>${FW.map((w) => `<option value="fav:${w}">★ ${esc(favName(w))}</option>`).join("")}${cats.map((c) => `<option value="${esc(c.id)}">${esc(c.name)}</option>`).join("")}</select></div><div id="pkList" class="pkList"></div>`);
  const draw = () => {
    const q = norm($("#pkQ").value), c = $("#pkCat").value;
    let a = S.items.live;
    if (c.slice(0, 4) === "fav:") a = a.filter((x) => isFav("live", x, c.slice(4)));
    else if (c !== "*") a = a.filter((x) => x.group === c);
    if (q) a = a.filter((x) => (x._n || (x._n = norm(x.name))).includes(q));
    const box = $("#pkList");
    chunked(box, a, (it) => {
      const d = liveRow(it);
      d.classList.remove("on");
      d.querySelector(".star").remove();
      return d;
    });
    if (!a.length) box.innerHTML = '<p class="muted" style="padding:14px">Nenhum canal encontrado.</p>';
  };
  $("#pkQ").oninput = draw;
  $("#pkCat").onchange = draw;
  $("#pkList").onclick = (e) => {
    const r = e.target.closest(".ch");
    if (!r) return;
    mvSlots()[i] = r._it.k;
    LS.set("mv", S.mvAll);
    MV.aud = i;
    closeModal();
    mvStart();
  };
  if (S.sel.live !== "*") $("#pkCat").value = S.sel.live;
  draw();
  setTimeout(() => $("#pkQ").focus(), 50);
}
const DLS = { items: [], dir: "", max: 1, timer: null, byK: /* @__PURE__ */ new Map(), sig: "", active: false, ok: true };
const fmtB = (b) => {
  b = +b || 0;
  const u = ["B", "KB", "MB", "GB", "TB"];
  let i = 0;
  while (b >= 1024 && i < 4) {
    b /= 1024;
    i++;
  }
  return b.toFixed(i >= 3 ? 2 : i ? 1 : 0).replace(".", ",") + " " + u[i];
};
const dlOf = (k) => DLS.items.find((x) => x.k === k && x.status !== "erro") || null;
const dlDone = (k) => {
  const d = DLS.byK.get(k);
  return d || null;
};
function dlFetch() {
  return __async(this, null, function* () {
    if (WEBOS) return;
    try {
      let j;
      if (AND) j = JSON.parse(AND.post("/dl/list", "{}"));
      else {
        const r = yield fetch("/dl/list");
        if (!r.ok) throw 0;
        j = yield r.json();
      }
      DLS.ok = true;
      DLS.items = j.items || [];
      DLS.dir = j.dir;
      DLS.max = j.max;
      DLS.byK = new Map(DLS.items.filter((x) => x.status === "concluido" && x.exists && x.k).map((x) => [x.k, x]));
      DLS.active = DLS.items.some((x) => x.status === "baixando" || x.status === "fila");
    } catch (e) {
      DLS.ok = false;
    }
    dlBadge();
    if (S.view === "dl") renderDl();
    clearTimeout(DLS.timer);
    DLS.timer = setTimeout(dlFetch, DLS.active || S.view === "dl" ? 1e3 : 2e4);
  });
}
function dlPost(path, body) {
  return __async(this, null, function* () {
    if (AND) {
      const j2 = JSON.parse(AND.post(path, JSON.stringify(body || {})));
      if (j2.erro) throw new Error(j2.erro);
      return j2;
    }
    const r = yield fetch(path, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(body || {}) });
    const j = yield r.json().catch(() => ({}));
    if (!r.ok) throw new Error(j.erro || "HTTP " + r.status);
    return j;
  });
}
function dlAdd(items) {
  return __async(this, null, function* () {
    try {
      const j = yield dlPost("/dl/add", { items, ua: S.cfg.ua });
      toast(j.added ? (j.added === 1 ? "Download adicionado" : `${j.added} downloads adicionados`) + ". Acompanhe na aba Downloads." : "Isso já está na sua lista de downloads.");
      yield dlFetch();
    } catch (e) {
      toast("Não consegui iniciar o download: " + e.message + (String(e.message).includes("404") ? " (feche e abra o berga_tv.py novo)" : ""), true);
    }
  });
}
function dlBadge() {
  const n = DLS.items.filter((x) => x.kind !== "rec" && (x.status === "baixando" || x.status === "fila")).length;
  const b = $("#dlBadge");
  b.textContent = n;
  b.style.display = n ? "inline-block" : "none";
}
function dlTxt(d) {
  if (d.status === "baixando") {
    const left = d.speed && d.total ? (d.total - d.done) / d.speed : 0;
    return `${fmtB(d.done)} de ${d.total ? fmtB(d.total) : "?"}${d.speed ? " · " + fmtB(d.speed) + "/s" : ""}${left ? " · faltam " + (left < 60 ? "menos de 1 min" : (left > 3600 ? Math.floor(left / 3600) + "h " : "") + Math.ceil(left % 3600 / 60) + " min") : ""}`;
  }
  if (d.status === "fila") return "Na fila" + (d.done ? ` · ${fmtB(d.done)} já baixados` : "");
  if (d.status === "pausado") return "Pausado" + (d.total ? ` em ${Math.floor(d.done / d.total * 100)}%` : "") + (d.msg ? " · " + d.msg : "");
  if (d.status === "erro") return "Erro: " + d.msg;
  return d.exists ? `${fmtB(d.total)} · concluído` : "Arquivo não encontrado (foi apagado ou movido)";
}
function dlBtns(d) {
  const b = (a, t, c = "") => `<button class="btn sm ${c}" data-dla="${a}" data-id="${d.id}">${t}</button>`;
  if (d.status === "concluido") return (d.exists ? b("play", "▶ Assistir", "pri") + b("folder", "📂 Pasta") : "") + (d.exists ? b("delete", "Apagar arquivo", "danger") : "") + b("remove", "Tirar da lista");
  if (AND) return b("cancel", "Cancelar", "danger");
  return (d.status === "baixando" || d.status === "fila" ? b("pause", "⏸ Pausar") : b("resume", "▶ Retomar", "pri")) + b("cancel", "Cancelar", "danger");
}
function renderDl(force) {
  const box = $("#dlBox");
  const its = DLS.items.filter((x) => x.kind !== "rec"), act = its.filter((x) => x.status !== "concluido"), done = its.filter((x) => x.status === "concluido").sort((a, b) => (b.finished || 0) - (a.finished || 0));
  const sig = DLS.ok + "|" + DLS.dir + "|" + DLS.max + "|" + [...act, ...done].map((x) => x.id + x.status + (x.exists ? 1 : 0)).join(",");
  if (!force && sig === DLS.sig) {
    act.forEach((d) => {
      const r = box.querySelector(`.dlRow[data-id="${d.id}"]`);
      if (!r) return;
      r.querySelector(".dlSt").textContent = dlTxt(d);
      const i = r.querySelector(".bar i");
      if (i) i.style.width = (d.total ? d.done / d.total * 100 : 0) + "%";
    });
    return;
  }
  DLS.sig = sig;
  const row = (d) => `<div class="dlRow" data-id="${d.id}"><img ${d.logo ? `src="${esc(d.logo)}"` : ""} alt=""><div class="dlMain"><b>${esc(d.name)}</b>${d.status !== "concluido" ? `<div class="bar"><i style="width:${d.total ? d.done / d.total * 100 : 0}%"></i></div>` : ""}<div class="dlSt${d.status === "erro" || d.status === "concluido" && !d.exists ? " err" : ""}">${esc(dlTxt(d))}</div></div><div class="dlBtns">${dlBtns(d)}</div></div>`;
  box.innerHTML = (DLS.ok ? "" : '<p class="dlSt err">O servidor do app não respondeu. Ele está aberto?</p>') + `<div class="dlHead"><div class="path"><span class="muted small">Salvando em</span><br><b>${esc(DLS.dir || "…")}</b></div><button class="btn sm" data-dla="openroot">📂 Abrir pasta</button>${AND ? "" : '<button class="btn sm" data-dla="cfg">Alterar pasta / simultâneos</button>'}</div><p class="muted small" style="margin:6px 2px 18px">Cada download usa uma conexão do seu plano. Se o plano permitir só 1 conexão, a TV ao vivo pode travar enquanto baixa. Os arquivos ficam no computador mesmo depois de vencer a lista.</p>` + (act.length ? `<h3>Em andamento (${act.length})</h3>` + act.map(row).join("") : "") + (done.length ? `<h3>Baixados (${done.length})</h3>` + done.map(row).join("") : "") + (!act.length && !done.length ? '<p class="muted">Nenhum download ainda. Abra um filme ou série e toque em <b>⬇ Baixar</b>.</p>' : "");
}
function playDownloaded(d) {
  playVod({ k: d.k || "dl|" + d.id, name: d.name, logo: d.logo, url: AND ? "dl:" + d.id : "/dl/file/" + d.id + d.ext });
}
function movieDl(it) {
  return { k: it.k, name: it.name, url: it.url, logo: it.logo, kind: "movie", folder: ["Filmes"], filename: it.name };
}
function dlLabel(k, full) {
  const d = dlOf(k);
  if (!d) return full ? "⬇ Baixar" : "⬇";
  if (d.status === "concluido") return full ? "✓ Baixado" : "✓";
  return full ? "⬇ Baixando…" : "⏳";
}
let zapT;
function playLive(it, delay) {
  S.cur = it;
  S.liveOn = true;
  document.querySelectorAll("#liveList .ch").forEach((e) => {
    const on = e._it === it;
    e.classList.toggle("on", on);
    if (on && delay !== void 0) e.scrollIntoView({ block: "nearest" });
  });
  renderLiveInfo();
  clearTimeout(zapT);
  vmsg("live", "Carregando…");
  const go = () => {
    if (S.cur !== it) return;
    if (vodOpen() || S.view === "multi") return placePlayer();
    startLive(it);
    placePlayer();
  };
  if (delay) zapT = setTimeout(go, delay);
  else go();
}
function zap(d) {
  const list = itemsOf("live");
  if (!list.length) return;
  let i = S.cur ? list.indexOf(S.cur) : -1;
  i = i < 0 ? 0 : (i + d + list.length) % list.length;
  playLive(list[i], 350);
}
function openMovie(it) {
  return __async(this, null, function* () {
    S.modalFor = it;
    const pr = S.prog[it.k];
    let inf = {};
    const draw = () => {
      const r = parseFloat(it.rating);
      modal(`<button class="mx" data-close>✕</button>${inf.backdrop ? '<div class="mBack"></div>' : ""}<div class="mHead"><img class="mPoster" ${it.logo ? `src="${esc(it.logo)}"` : ""} alt=""><div class="mMeta"><h2>${esc(inf.name || it.name)}</h2><div class="tags">${[inf.year, inf.genre, inf.duration, r > 0 ? "★ " + r.toFixed(1) : ""].filter(Boolean).map((x) => `<span>${esc(x)}</span>`).join("")}</div><p>${esc(inf.plot || (S.x ? "Carregando detalhes…" : ""))}</p>${inf.cast ? `<p class="muted small"><b>Elenco:</b> ${esc(inf.cast)}</p>` : ""}${inf.director ? `<p class="muted small"><b>Direção:</b> ${esc(inf.director)}</p>` : ""}<div class="mBtns">${pr && pr.t > 20 ? `<button class="btn pri" data-a="resume">▶ Continuar de ${fmtDur(pr.t)}</button><button class="btn" data-a="play">Do início</button>` : `<button class="btn pri" data-a="play">▶ Assistir</button>`}${FW.map((w) => `<button class="btn" data-a="fav" data-w="${w}">${esc(favBtnTxt("movie", it, w))}</button>`).join("")}<button class="btn" data-a="dl">${dlLabel(it.k, true)}</button></div>${dlDone(it.k) ? '<p class="muted small" style="margin-top:10px">✓ Baixado no computador: o play usa o arquivo, sem gastar conexão nem internet.</p>' : ""}</div></div>`);
      if (inf.backdrop) {
        const b = $(".mBack");
        b && b.style.setProperty("--bd", `url("${String(inf.backdrop).replace(/"/g, "%22")}")`);
      }
    };
    draw();
    $("#modalCard").onclick = (e) => {
      const b = e.target.closest("[data-a]");
      if (!b) return;
      const a = b.dataset.a;
      if (a === "play" || a === "resume") {
        closeModal();
        playVod(it, { start: a === "resume" ? pr.t : 0 });
      } else if (a === "fav") {
        toggleFav("movie", it, b.dataset.w);
        b.textContent = favBtnTxt("movie", it, b.dataset.w);
      } else if (a === "dl") {
        const d = dlOf(it.k);
        if (d) {
          closeModal();
          setView("dl");
          return;
        }
        b.textContent = "⬇ Baixando…";
        dlAdd([movieDl(it)]);
      }
    };
    if (S.x && it.xid) {
      try {
        const j = JSON.parse(yield txt(xapi("get_vod_info", "&vod_id=" + it.xid)));
        const i = j.info || {};
        inf = { name: i.name || i.o_name, plot: i.plot || i.description, cast: i.cast || i.actors, director: i.director, genre: i.genre, year: String(i.releasedate || i.release_date || "").slice(0, 4), duration: i.duration, backdrop: [].concat(i.backdrop_path || [])[0] };
      } catch (e) {
        inf = { plot: " " };
      }
      if (S.modalFor === it) draw();
    }
  });
}
function openSeries(it) {
  return __async(this, null, function* () {
    S.modalFor = it;
    let seasons = null, info = { plot: it.plot, year: it.year }, cur = null, err = "";
    const draw = () => {
      const head = `<button class="mx" data-close>✕</button>${info.backdrop ? '<div class="mBack"></div>' : ""}<div class="mHead"><img class="mPoster" ${it.logo ? `src="${esc(it.logo)}"` : ""} alt=""><div class="mMeta"><h2>${esc(it.name)}</h2><div class="tags">${[info.year, info.genre, parseFloat(it.rating) > 0 ? "★ " + parseFloat(it.rating).toFixed(1) : ""].filter(Boolean).map((x) => `<span>${esc(x)}</span>`).join("")}</div><p>${esc(info.plot || "")}</p>${info.cast ? `<p class="muted small"><b>Elenco:</b> ${esc(info.cast)}</p>` : ""}<div class="mBtns">${FW.map((w) => `<button class="btn" data-a="fav" data-w="${w}">${esc(favBtnTxt("series", it, w))}</button>`).join("")}</div></div></div>`;
      let body = "";
      if (!seasons) body = `<p class="muted">${err ? "Não foi possível carregar os episódios: " + esc(err) : "Carregando episódios…"}</p>`;
      else if (!seasons.size) body = '<p class="muted">Nenhum episódio disponível.</p>';
      else {
        if (cur == null || !seasons.has(cur)) cur = [...seasons.keys()][0];
        body = `<div class="seasons">${[...seasons.keys()].map((s) => `<button data-s="${s}" class="${s === cur ? "on" : ""}">Temporada ${s}</button>`).join("")}<span style="flex:1"></span><button class="btn sm" data-a="dlseason">⬇ Baixar temporada ${cur}</button></div>` + seasons.get(cur).map((e, i) => {
          const pr = S.prog[e.k];
          return `<div class="epi" tabindex="0" data-i="${i}">${e.img ? `<img loading="lazy" src="${esc(e.img)}" alt="">` : ""}<span class="en">${e.e}</span><div class="et"><b>${esc(e.title)}</b>${e.plot ? `<p>${esc(e.plot)}</p>` : ""}${pr && pr.d ? `<div class="bar"><i style="width:${Math.min(100, pr.t / pr.d * 100)}%"></i></div>` : ""}</div><span class="muted small">${esc(e.dur || "")}</span><button class="btn sm dlb${dlDone(e.k) ? " ok" : ""}" data-dl="${i}" title="Baixar episódio">${dlLabel(e.k)}</button></div>`;
        }).join("");
      }
      modal(head + body);
      if (info.backdrop) {
        const b = $(".mBack");
        b && b.style.setProperty("--bd", `url("${String(info.backdrop).replace(/"/g, "%22")}")`);
      }
    };
    const group = (eps) => {
      const m = /* @__PURE__ */ new Map();
      eps.forEach((e) => {
        if (!m.has(e.s)) m.set(e.s, []);
        m.get(e.s).push(e);
      });
      for (const l of m.values()) l.sort((a, b) => a.e - b.e);
      return new Map([...m.entries()].sort((a, b) => a[0] - b[0]));
    };
    const label = (e) => `${it.name} · T${e.s}E${String(e.e).padStart(2, "0")}${e.title && e.title !== it.name ? " – " + e.title : ""}`;
    $("#modalCard").onclick = (e) => {
      const sb = e.target.closest("[data-s]");
      if (sb) {
        cur = +sb.dataset.s;
        draw();
        return;
      }
      const fb = e.target.closest('[data-a="fav"]');
      if (fb) {
        toggleFav("series", it, fb.dataset.w);
        fb.textContent = favBtnTxt("series", it, fb.dataset.w);
        return;
      }
      const pad = (n) => String(n).padStart(2, "0"), epDl = (x) => ({ k: x.k, name: label(x), url: x.url, logo: it.logo, kind: "series", folder: ["Séries", it.name, "Temporada " + x.s], filename: `${it.name} - T${pad(x.s)}E${pad(x.e)}${x.title && !/^Episódio \d+$/.test(x.title) && x.title !== it.name ? " - " + x.title : ""}` });
      const db = e.target.closest("[data-dl]");
      if (db) {
        const x = seasons.get(cur)[+db.dataset.dl];
        if (dlOf(x.k)) {
          closeModal();
          setView("dl");
          return;
        }
        db.textContent = "…";
        dlAdd([epDl(x)]).then(draw);
        return;
      }
      if (e.target.closest('[data-a="dlseason"]')) {
        const l = seasons.get(cur).filter((x) => !dlOf(x.k));
        if (!l.length) return toast("Todos os episódios desta temporada já estão nos downloads.");
        dlAdd(l.map(epDl)).then(draw);
        return;
      }
      const ep = e.target.closest(".epi");
      if (ep) {
        const all = [...seasons.values()].flat(), list = seasons.get(cur), e0 = list[+ep.dataset.i], idx = all.indexOf(e0);
        const mk = (x) => ({ k: x.k, name: label(x), logo: it.logo, url: x.url, series: it.k });
        const pr = S.prog[e0.k];
        closeModal();
        playVod(mk(e0), { start: pr && pr.t > 20 ? pr.t : 0, queue: all.slice(idx + 1).map(mk) });
      }
    };
    if (it.eps) {
      seasons = group(it.eps.map((e) => __spreadProps(__spreadValues({}, e), { k: it.k + "|" + e.s + "x" + e.e })));
      draw();
      return;
    }
    draw();
    try {
      const j = JSON.parse(yield txt(xapi("get_series_info", "&series_id=" + it.xid)));
      const i = j.info || {};
      info = { plot: i.plot || it.plot, year: String(i.releaseDate || i.release_date || it.year || "").slice(0, 4), genre: i.genre, cast: i.cast, backdrop: [].concat(i.backdrop_path || [])[0] };
      const B = S.x.base, U = enc(S.x.u), P = enc(S.x.p), eps = [];
      for (const [sn, list] of Object.entries(j.episodes || {})) for (const e of arr(list)) eps.push({ s: +e.season || +sn || 1, e: +e.episode_num || 0, title: e.title || "Episódio " + e.episode_num, url: `${B}/series/${U}/${P}/${e.id}.${e.container_extension || "mp4"}`, k: S.src.id + "|e|" + e.id, plot: e.info && e.info.plot || "", img: e.info && e.info.movie_image || "", dur: e.info && e.info.duration || "" });
      seasons = group(eps);
    } catch (e) {
      err = e.message;
    }
    if (S.modalFor === it) draw();
  });
}
function playVod(it, o = {}) {
  if (AND) {
    const items = [it, ...o.queue || []].map((x) => {
      const dd = x.url.startsWith("dl:") ? null : dlDone(x.k);
      S.nativeIts[x.k] = snap(x);
      return { k: x.k, name: x.name, logo: x.logo || "", url: dd ? "dl:" + dd.id : x.url };
    });
    nativePlay({ mode: "vod", items, index: 0, start: Math.round((o.start || 0) * 1e3) });
    return;
  }
  const v = $("#vodVideo"), P = $("#vodPlayer");
  const d = it.url[0] !== "/" && dlDone(it.k);
  if (d) it = __spreadProps(__spreadValues({}, it), { url: "/dl/file/" + d.id + d.ext });
  P.classList.remove("hidden");
  syncLive();
  mvStop();
  $("#vodTitle").textContent = it.name;
  S.vod = { it, queue: o.queue || [] };
  $("#vodNext").classList.toggle("hidden", !S.vod.queue.length);
  vmsg("vod", "Carregando…");
  playStream(v, it.url, { live: false, which: "vod", onErr: (m) => vmsg("vod", m) });
  if (o.start > 0) {
    const seek = () => {
      v.removeEventListener("loadedmetadata", seek);
      try {
        v.currentTime = o.start;
      } catch (e) {
      }
    };
    v.addEventListener("loadedmetadata", seek);
  }
  idleKick();
}
function closeVod() {
  saveProg(true);
  if (document.fullscreenElement) document.exitFullscreen().catch(() => {
  });
  stopVideo($("#vodVideo"));
  vmsg("vod", "");
  $("#vodPlayer").classList.add("hidden");
  S.vod = null;
  if (S.view === "fav") renderFav();
  if (S.view === "movie") renderItems("movie");
  if (S.view === "multi") mvStart();
  syncLive();
}
function nextEp() {
  const V = S.vod;
  if (!V || !V.queue.length) return;
  saveProg(true);
  const n = V.queue.shift();
  const pr = S.prog[n.k];
  playVod(n, { queue: V.queue, start: pr && pr.t > 20 ? pr.t : 0 });
}
let idleT;
function idleKick() {
  const P = $("#vodPlayer");
  P.classList.remove("idle");
  clearTimeout(idleT);
  idleT = setTimeout(() => {
    if (!$("#vodVideo").paused) P.classList.add("idle");
  }, 3e3);
}
const PUBLIC = [
  { id: "br", name: "Canais abertos do Brasil", desc: "iptv-org · TVs abertas, educativas, legislativas e regionais", url: "https://iptv-org.github.io/iptv/countries/br.m3u" },
  { id: "por", name: "Canais em português (Brasil e Portugal)", desc: "iptv-org · lista maior, inclui canais portugueses", url: "https://iptv-org.github.io/iptv/languages/por.m3u" }
];
function acctHtml() {
  var _a, _b;
  const a = S.acct;
  if (!a) return "";
  const exp = a.exp ? new Date(a.exp * 1e3) : null, days = exp ? Math.ceil((exp - Date.now()) / 864e5) : null;
  return `<h3>Conta Xtream</h3><div class="acct"><div><span class="muted small">Status</span><b>${esc(a.status || "—")}</b></div><div><span class="muted small">Vencimento</span><b>${exp ? exp.toLocaleDateString("pt-BR") + (days != null ? ` (${days} dias)` : "") : "Sem data"}</b></div><div><span class="muted small">Conexões</span><b>${esc((_a = a.active) != null ? _a : "?")} / ${esc((_b = a.max) != null ? _b : "?")}</b></div><div><span class="muted small">Formato ao vivo</span><b>${esc((a.fmt || "").toUpperCase())}</b></div></div>`;
}
function openSettings(edit) {
  S.modalFor = "settings";
  const e = edit ? S.sources.find((s) => s.id === edit) : null, type = e ? e.type : "m3u";
  modal(`<button class="mx" data-close>✕</button><h2>Configurações</h2>
  <h3>Minhas listas</h3>${S.sources.map((s) => `<div class="src${s.id === S.active ? " on" : ""}"><div><b>${esc(s.name)}</b><div class="muted small">${s.type === "xtream" ? "Xtream · " + esc(hostOf(s.server)) + " · " + esc(s.user) : s.file ? "Arquivo M3U" : "M3U · " + esc(hostOf(s.url))}</div></div><div class="srcBtns">${s.id === S.active ? '<span class="pill">Em uso</span>' : `<button class="btn sm" data-use="${s.id}">Usar</button>`}<button class="btn sm" data-ref="${s.id}">Atualizar</button><button class="btn sm" data-edit="${s.id}">Editar</button><button class="btn sm danger" data-del="${s.id}">Remover</button></div></div>`).join("") || '<p class="muted">Nenhuma lista cadastrada ainda.</p>'}
  ${acctHtml()}
  ${e ? "" : `<h3>Listas gratuitas e legais</h3><p class="muted small" style="margin-top:-4px">Canais abertos que as próprias emissoras liberam na internet, reunidos pelo projeto iptv-org. Não tem filmes nem séries; alguns canais podem estar fora do ar.</p>${PUBLIC.map((x) => `<div class="pub"><div><b>${esc(x.name)}</b><div class="muted small">${esc(x.desc)}</div></div>${S.sources.some((s) => s.url === x.url) ? '<span class="pill">Adicionada</span>' : `<button class="btn sm" data-pub="${x.id}">+ Adicionar</button>`}</div>`).join("")}`}
  <h3>${e ? "Editar lista: " + esc(e.name) : "Adicionar lista"}</h3>
  <div class="tabs">${e ? "" : `<button data-tab="m3u" class="${type === "m3u" ? "on" : ""}">Lista M3U</button><button data-tab="xtream" class="${type === "xtream" ? "on" : ""}">Xtream Codes</button>`}</div>
  <form id="srcForm" data-type="${type}" ${e ? `data-edit="${e.id}"` : ""} autocomplete="off">
    <label>Nome (opcional)<input name="name" value="${esc(e ? e.name : "")}" placeholder="Ex.: Minha lista"></label>
    <div class="only-m3u"><label>URL da lista M3U<input name="url" value="${esc(e && e.url || "")}" placeholder="http://provedor.com/lista.m3u"></label>${WEBOS ? "" : `<label>…ou um arquivo .m3u do computador${e && e.file ? " (já enviado; escolha outro para trocar)" : ""}<input type="file" name="file" accept=".m3u,.m3u8,.txt"></label>`}</div>
    <div class="only-xtream"><label>Servidor (com porta)<input name="server" value="${esc(e && e.server || "")}" placeholder="http://servidor.com:8080"></label><div class="row2"><label>Usuário<input name="user" value="${esc(e && e.user || "")}"></label><label>Senha<input name="pass" type="password" placeholder="${e ? "(manter a atual)" : ""}"></label></div></div>
    <label>URL do guia de programação EPG (opcional)<input name="epg" value="${esc(e && e.epg || "")}" placeholder="Deixe em branco para usar o da lista"></label>
    <div class="mBtns"><button class="btn pri" type="submit">${e ? "Salvar alterações" : "Salvar e carregar"}</button>${e ? '<button class="btn" type="button" data-cancel>Cancelar</button>' : ""}</div>
  </form>
  ${AND ? `<h3>Atualização</h3><div class="pub"><div><b>Berga TV ${esc(appVer().name)}</b><div class="muted small" id="updSt">${UPD.info && !UPD.info.erro ? UPD.info.latest > UPD.info.current ? "Nova versão " + esc(UPD.info.name) + " disponível." : "Você está na versão mais recente." : "Toque para verificar se há versão nova."}</div></div><button class="btn sm" type="button" data-upd>Verificar atualização</button></div>` : ""}
  ${WEBOS ? `<h3>TV LG</h3><div class="pub"><div><b>Berga TV ${esc(window.BERGA_VERSION || "")}</b><div class="muted small">Modo desenvolvedor renovado há ${Math.floor((Date.now() - LS.get("devRenewAt", Date.now())) / 864e5)} dias (vence com 41). Renove no Dev Manager → Info → Renew session.</div></div><button class="btn sm" type="button" data-devok>Acabei de renovar</button></div>` : ""}
  <h3>Preferências</h3>
  <form id="cfgForm">
    <div class="row2"><label>Formato dos canais ao vivo (Xtream)<select name="fmt"><option value="auto">Automático</option><option value="m3u8">HLS (.m3u8)</option><option value="ts">MPEG-TS (.ts)</option></select></label>
    <label>User-Agent enviado ao provedor<input name="ua" value="${esc(S.cfg.ua)}" placeholder="Padrão: VLC"></label></div>
    ${AND || WEBOS ? "" : `<div class="row2"><label>Pasta dos downloads<input name="dldir" value="${esc(DLS.dir)}"></label><label>Downloads ao mesmo tempo<select name="dlmax">${[1, 2, 3, 4].map((n) => `<option value="${n}" ${+DLS.max === n ? "selected" : ""}>${n}</option>`).join("")}</select></label></div>`}
    <div class="row2"><label>Nome dos favoritos 1 (estrela rosa)<input name="favF" value="${esc(S.cfg.favF)}"></label><label>Nome dos favoritos 2 (estrela amarela)<input name="favB" value="${esc(S.cfg.favB)}"></label></div>
    ${AND || WEBOS ? `<label>Computador que grava os programas (endereço do Berga TV no PC, ex.: 192.168.1.24:8765)<input name="pcAddr" value="${esc(S.cfg.pcAddr)}" placeholder="Abra o atalho Berga TV (rede Wi-Fi) no PC e copie o endereço"></label>` : ""}
    <label class="chk"><input type="checkbox" name="hideAdult" ${S.cfg.hideAdult ? "checked" : ""}> Ocultar categorias adultas</label>
    <div class="mBtns"><button class="btn" type="submit">Salvar preferências</button><button class="btn" type="button" data-epg>Recarregar guia (EPG)</button></div>
  </form>
  ${AND || WEBOS ? "" : `<p class="muted small" style="margin-top:18px">Dica: para abrir na TV ou em outro aparelho da mesma rede Wi-Fi, rode <b>python berga_tv.py --lan</b> e acesse o endereço que aparece na janela.</p>`}`);
  $("#cfgForm").fmt.value = S.cfg.fmt;
  const card2 = $("#modalCard");
  card2.onclick = (ev) => __async(this, null, function* () {
    const b = ev.target.closest("button");
    if (!b) return;
    const d = b.dataset;
    if (d.tab) {
      $("#srcForm").dataset.type = d.tab;
      card2.querySelectorAll("[data-tab]").forEach((x) => x.classList.toggle("on", x === b));
      return;
    }
    if (d.use) {
      S.active = d.use;
      closeModal();
      loadActive(false);
      return;
    }
    if (d.ref) {
      S.active = d.ref;
      closeModal();
      loadActive(true);
      return;
    }
    if (d.edit) {
      openSettings(d.edit);
      return;
    }
    if (d.cancel !== void 0) {
      openSettings();
      return;
    }
    if (d.epg !== void 0) {
      if (S.src) {
        closeModal();
        loadEPG(S.src, true);
      }
      return;
    }
    if (d.devok !== void 0) {
      LS.set("devRenewAt", Date.now());
      toast("Anotado. Aviso de novo daqui a 30 dias.");
      openSettings();
      return;
    }
    if (d.upd !== void 0) {
      if (UPD.info && UPD.info.latest > UPD.info.current && UPD.info.url) {
        updModal(UPD.info);
        return;
      }
      updCheck(true);
      return;
    }
    if (d.pub) {
      const x = PUBLIC.find((y) => y.id === d.pub);
      const s = { id: "s" + Date.now().toString(36), type: "m3u", name: x.name, url: x.url, epg: "" };
      S.sources.push(s);
      LS.set("sources", S.sources);
      S.active = s.id;
      closeModal();
      loadActive(true);
      return;
    }
    if (d.del) {
      const s = S.sources.find((x) => x.id === d.del);
      if (!s || !confirm('Remover a lista "' + s.name + '"?')) return;
      S.sources = S.sources.filter((x) => x.id !== d.del);
      LS.set("sources", S.sources);
      delete S.favs[d.del];
      LS.set("favs", S.favs);
      idb.del("cat:" + d.del).catch(() => {
      });
      idb.del("file:" + d.del).catch(() => {
      });
      if (S.active === d.del) {
        S.active = S.sources[0] ? S.sources[0].id : null;
        yield loadActive(false);
      }
      openSettings();
    }
  });
  card2.onsubmit = (ev) => __async(this, null, function* () {
    ev.preventDefault();
    const f = ev.target;
    if (f.id === "cfgForm") {
      const old2 = S.cfg.fmt;
      S.cfg = { ua: f.ua.value.trim(), fmt: f.fmt.value, hideAdult: f.hideAdult.checked, favF: f.favF.value.trim() || "Fran", favB: f.favB.value.trim() || "Berga", pcAddr: f.pcAddr ? normPc(f.pcAddr.value) : S.cfg.pcAddr };
      REC.sig = "";
      LS.set("cfg", S.cfg);
      const dd = f.dldir ? f.dldir.value.trim() : "", dm = f.dlmax ? +f.dlmax.value : +DLS.max;
      if (!AND && (dd && dd !== DLS.dir) || dm !== +DLS.max) {
        try {
          yield dlPost("/dl/config", { dir: dd, max: dm });
          yield dlFetch();
        } catch (err) {
          return toast("Não consegui usar essa pasta: " + err.message, true);
        }
      }
      closeModal();
      toast("Preferências salvas");
      if (old2 !== S.cfg.fmt && S.src && S.src.type === "xtream") loadActive(true);
      else renderAll();
      return;
    }
    const fd = new FormData(f), editId = f.dataset.edit || null, old = editId && S.sources.find((x) => x.id === editId);
    let s = { id: editId || "s" + Date.now().toString(36), type: f.dataset.type, name: String(fd.get("name") || "").trim(), epg: String(fd.get("epg") || "").trim() };
    if (s.type === "m3u") {
      const url = String(fd.get("url") || "").trim(), file = fd.get("file");
      const xm = url.match(/^(https?:\/\/[^/]+)\/get\.php\?(.*)$/i);
      if (xm) {
        const p = new URLSearchParams(xm[2]);
        if (p.get("username") && p.get("password")) {
          s = __spreadProps(__spreadValues({}, s), { type: "xtream", server: xm[1], user: p.get("username"), pass: p.get("password") });
          toast("Detectei um login Xtream na URL e cadastrei como Xtream — assim você tem filmes, séries e guia completos.");
        }
      }
      if (s.type === "m3u") {
        if (file && file.size) {
          s.file = true;
          yield idb.set("file:" + s.id, yield file.text());
        } else if (url) s.url = url;
        else if (old && old.file) s.file = true;
        else return toast("Informe a URL da lista ou escolha um arquivo.", true);
      }
    } else {
      s.server = String(fd.get("server") || "").trim();
      s.user = String(fd.get("user") || "").trim();
      s.pass = String(fd.get("pass") || "") || old && old.pass || "";
      if (!s.server || !s.user || !s.pass) return toast("Preencha servidor, usuário e senha.", true);
    }
    if (!s.name) s.name = s.type === "xtream" ? s.user + " @ " + hostOf(s.server) : s.url ? hostOf(s.url) : "Lista " + (S.sources.length + 1);
    const i = S.sources.findIndex((x) => x.id === s.id);
    if (i >= 0) S.sources[i] = s;
    else S.sources.push(s);
    LS.set("sources", S.sources);
    S.active = s.id;
    closeModal();
    yield loadActive(true);
  });
}
$("#nav").onclick = (e) => {
  const b = e.target.closest("button");
  if (b) setView(b.dataset.view);
};
$("#btnSettings").onclick = () => openSettings();
$("#emptyAdd").onclick = () => openSettings();
$("#modal").addEventListener("click", (e) => {
  if (e.target.id === "modal" || e.target.closest("[data-close]")) closeModal();
});
["live", "movie", "series"].forEach((t) => {
  $("#" + t + "Cats").onclick = (e) => {
    const c = e.target.closest(".cat");
    if (!c) return;
    S.sel[t] = c.dataset.id;
    if (S.q) {
      S.q = "";
      $("#q").value = "";
    }
    renderCats(t);
    renderItems(t);
    const b = t === "live" ? $("#liveList") : $("#" + t + "Grid");
    b.scrollTop = 0;
  };
});
$("#liveList").onclick = (e) => {
  const r = e.target.closest(".ch");
  if (!r) return;
  const st = e.target.closest(".star");
  if (st) return toggleFav("live", r._it, st.dataset.w);
  if ((AND || TV) && S.cur === r._it && S.liveOn) return liveFull();
  playLive(r._it);
};
["movie", "series"].forEach((t) => {
  $("#" + t + "Grid").onclick = (e) => {
    const c = e.target.closest(".card");
    if (!c) return;
    const st = e.target.closest(".star");
    if (st) return toggleFav(t, c._it, st.dataset.w);
    t === "movie" ? openMovie(c._it) : openSeries(c._it);
  };
});
$("#favBox").onclick = (e) => {
  const ft = e.target.closest("[data-ft]");
  if (ft) {
    S.favTab = ft.dataset.ft;
    LS.set("favTab", S.favTab);
    renderFav();
    return;
  }
  const r = e.target.closest(".ch,.card");
  if (!r) return;
  const it = r._it;
  const st0 = e.target.closest(".star");
  if (r.classList.contains("ch")) {
    if (st0) return toggleFav("live", it, st0.dataset.w);
    const real = S.items.live.find((i) => i.k === it.k) || it;
    setView("live");
    playLive(real);
    return;
  }
  if (r._t === "cont") {
    const pr = S.prog[it.k];
    if (e.target.closest(".star")) {
      delete S.prog[it.k];
      LS.set("prog", S.prog);
      renderFav();
      return;
    }
    playVod(it, { start: pr ? pr.t : 0 });
    return;
  }
  if (st0) return toggleFav(r._t, it, st0.dataset.w);
  r._t === "movie" ? openMovie(it) : openSeries(it);
};
$("#liveInfo").onclick = (e) => {
  const b = e.target.closest("[data-a]");
  if (!b || !S.cur) return;
  const a = b.dataset.a;
  if (a === "fav") toggleFav("live", S.cur, b.dataset.w);
  else if (a === "pip") pip();
  else if (a === "golive") goLive();
  else if (a === "arch") openArchive(S.cur);
  else liveFull();
};
$("#liveEpg").onclick = (e) => {
  const r = e.target.closest(".ep");
  if (!r || !S.cur) return;
  const a = epgOf(S.cur) || [], p = a.find((x) => x[0] === +r.dataset.s);
  if (p) progModal(S.cur, p);
};
$("#liveVideo").addEventListener("dblclick", (e) => {
  e.preventDefault();
  liveFull();
});
$("#guideCat").onchange = (e) => {
  S.guideCat = e.target.value;
  renderGuide();
};
$("#guideNow").onclick = () => renderGuide();
$("#guide").onclick = (e) => {
  const r = e.target.closest(".gRow");
  if (!r) return;
  const it = $("#guide")._chs[+r.dataset.i];
  if (!it) return;
  const pb = e.target.closest(".gProg[data-s]");
  if (pb) {
    const p = (epgOf(it) || []).find((x) => x[0] === +pb.dataset.s);
    if (p) return progModal(it, p);
  }
  setView("live");
  playLive(it);
};
$("#mvGrid").addEventListener("click", (e) => {
  const c = e.target.closest(".mvCell");
  if (!c) return;
  const i = +c.dataset.i, x = e.target.closest("[data-x]");
  if (x) {
    const a = x.dataset.x;
    if (a === "swap") return mvPick(i);
    if (a === "fs") return fs(c);
    if (a === "rm") {
      mvSlots()[i] = null;
      LS.set("mv", S.mvAll);
      stopVideo($("#mv" + i));
      vmsg("mv" + i, "");
      mvStart();
      return;
    }
  }
  if (!mvItem(i)) return mvPick(i);
  MV.aud = i;
  mvAudio();
  const v = $("#mv" + i);
  if (v.paused && v._k) {
    const p = v.play();
    p && p.catch && p.catch(() => {
    });
  }
});
$("#mvGrid").addEventListener("dblclick", (e) => {
  const c = e.target.closest(".mvCell");
  if (c && mvItem(+c.dataset.i) && !e.target.closest("button")) fs(c);
});
document.querySelectorAll("#v-multi [data-l]").forEach((b) => b.onclick = () => {
  MV.layout = b.dataset.l;
  LS.set("mvLayout", MV.layout);
  mvBuild();
});
$("#mvFs").onclick = () => fs($("#mvWrap"));
$("#mvClear").onclick = () => {
  S.mvAll[S.src ? S.src.id : "~"] = [null, null, null, null];
  LS.set("mv", S.mvAll);
  mvStart();
};
$("#dlBox").onclick = (e) => __async(this, null, function* () {
  const b = e.target.closest("[data-dla]");
  if (!b) return;
  const a = b.dataset.dla, id = b.dataset.id, d = DLS.items.find((x) => x.id === id);
  try {
    if (a === "openroot") {
      yield dlPost("/dl/open", {});
      return;
    }
    if (a === "cfg") {
      openSettings();
      setTimeout(() => {
        const i = document.querySelector("#cfgForm [name=dldir]");
        i && (i.scrollIntoView({ block: "center" }), i.focus());
      }, 60);
      return;
    }
    if (a === "play" && d) return playDownloaded(d);
    if (a === "folder") return dlPost("/dl/open", { id });
    if (a === "delete" && !confirm('Apagar o arquivo "' + (d ? d.name : "") + '" do computador?')) return;
    if (a === "cancel" && !confirm("Cancelar o download e apagar a parte já baixada?")) return;
    b.disabled = true;
    yield dlPost("/dl/act", { id, act: a });
    yield dlFetch();
  } catch (err) {
    toast("Erro: " + err.message, true);
  }
});
$("#vodClose").onclick = closeVod;
$("#vodNext").onclick = nextEp;
$("#vodPlayer").addEventListener("mousemove", idleKick);
const vv = $("#vodVideo");
vv.addEventListener("timeupdate", () => {
  if (S.vod && (!S.vod.saved || Date.now() - S.vod.saved > 5e3)) {
    S.vod.saved = Date.now();
    saveProg();
  }
});
vv.addEventListener("ended", () => {
  if (!S.vod) return;
  saveProg(true);
  if (S.vod.queue.length) nextEp();
  else closeVod();
});
vv.addEventListener("pause", () => {
  saveProg();
  idleKick();
});
wireVideo($("#liveVideo"), "live");
wireVideo(vv, "vod");
let qT;
$("#q").addEventListener("input", (e) => {
  clearTimeout(qT);
  qT = setTimeout(() => {
    S.q = e.target.value.trim();
    if (S.q && ["guide", "multi", "dl"].includes(S.view)) setView("live");
    const t = S.view;
    if (t === "fav") renderFav();
    else if (["live", "movie", "series"].includes(t)) {
      renderCats(t);
      renderItems(t);
    }
  }, 250);
});
document.addEventListener("keydown", (e) => {
  if (TVBROWSER && (e.keyCode === 461 || e.keyCode === 10009)) {
    if (window.bergaBack()) e.preventDefault();
    return;
  }
  const typing = /^(input|select|textarea)$/i.test(e.target.tagName || ""), vodOpen2 = !$("#vodPlayer").classList.contains("hidden"), modalOpen = !$("#modal").classList.contains("hidden");
  if (e.key === "Escape" && oskOpen()) {
    oskClose(false);
    return;
  }
  if (e.key === "Escape") {
    if (vodOpen2 && !document.fullscreenElement) {
      closeVod();
      return;
    }
    if (modalOpen) {
      closeModal();
      return;
    }
    if (typing && e.target.id === "q" && S.q) {
      e.target.value = "";
      e.target.dispatchEvent(new Event("input"));
    }
    return;
  }
  if (OSKON && e.key === "Enter" && oskIsText(e.target) && !oskOpen()) {
    e.preventDefault();
    oskShow(e.target);
    return;
  }
  if (TV && /^Arrow/.test(e.key) && !(e.target.tagName === "SELECT")) {
    if (typing && (e.key === "ArrowLeft" || e.key === "ArrowRight")) return;
    e.preventDefault();
    spatial(e.key);
    return;
  }
  if (typing) return;
  if (e.key === "/") {
    e.preventDefault();
    $("#q").focus();
    return;
  }
  if (vodOpen2) {
    idleKick();
    if (e.key === "f" || e.key === "F") fs($("#vodPlayer"));
    else if (e.key === " ") {
      e.preventDefault();
      vv.paused ? vv.play() : vv.pause();
    } else if (e.key === "ArrowRight" && e.target !== vv) {
      vv.currentTime += 10;
    } else if (e.key === "ArrowLeft" && e.target !== vv) {
      vv.currentTime -= 10;
    } else if (e.key === "n" || e.key === "N") nextEp();
    return;
  }
  if (e.key === "Enter" && e.target.matches(".ch,.card,.cat,.epi,.mvCell,.gRow,.gName,.gProg,.ep,.arcRow")) {
    e.preventDefault();
    e.target.click();
    return;
  }
  if (modalOpen) return;
  if (S.view === "multi") {
    if (/^[1-4]$/.test(e.key) && mvItem(+e.key - 1)) {
      MV.aud = +e.key - 1;
      mvAudio();
    } else if (e.key === "f" || e.key === "F") fs($("#mvWrap"));
    return;
  }
  if (S.view === "live") {
    if ((e.key === "ArrowUp" || e.key === "ArrowDown") && e.target.matches(".cat")) {
      const sib = e.key === "ArrowUp" ? e.target.previousElementSibling : e.target.nextElementSibling;
      if (sib) {
        sib.focus();
        e.preventDefault();
      }
      return;
    }
    if (e.key === "ArrowUp" || e.key === "ArrowDown" || e.key === "PageUp" || e.key === "PageDown") {
      e.preventDefault();
      zap(e.key === "ArrowUp" || e.key === "PageUp" ? -1 : 1);
      return;
    }
    if (e.key === "f" || e.key === "F") liveFull();
  }
});
setInterval(() => {
  refreshNow();
  if (S.view === "live") renderLiveInfo();
}, 3e4);
function liveFull(pipMode) {
  if (!S.cur) return;
  if (!AND) return fs($("#liveWrap"));
  const list = itemsOf("live");
  let i = list.indexOf(S.cur), L = list;
  if (i < 0) {
    L = [S.cur];
    i = 0;
  }
  const st = Math.max(0, i - 1500), arr2 = L.slice(st, st + 3e3);
  nativePlay({ mode: "live", items: arr2.map((x) => ({ k: x.k, name: x.name, logo: x.logo || "", url: x.url, num: String(x.num || "") })), index: i - st, pip: !!pipMode });
}
function nativePlay(o) {
  if (!AND) return false;
  S.nativeOpen = true;
  syncLive();
  mvStop();
  try {
    AND.play(JSON.stringify(Object.assign({ ua: S.cfg.ua || "" }, o)));
  } catch (e) {
    S.nativeOpen = false;
    syncLive();
    toast("Erro ao abrir o player: " + e.message, true);
    return false;
  }
  return true;
}
window.onNativeClosed = function(j) {
  S.nativeOpen = false;
  try {
    j = typeof j === "string" ? JSON.parse(j) : j;
  } catch (e) {
    j = null;
  }
  if (j && j.mode === "vod") (j.watched || []).forEach((w) => {
    const it = S.nativeIts[w.k] || S.prog[w.k] && S.prog[w.k].it;
    if (!it || !(w.dur > 0)) return;
    const t = w.pos / 1e3, d = w.dur / 1e3;
    if (d - t < Math.max(60, d * 0.04)) delete S.prog[w.k];
    else if (t >= 20) S.prog[w.k] = { t, d, at: Date.now(), it };
  });
  LS.set("prog", S.prog);
  if (j && j.mode === "live" && j.k) {
    const it = S.items.live.find((x) => x.k === j.k);
    if (it && it !== S.cur) {
      S.cur = it;
      renderLiveInfo();
      document.querySelectorAll("#liveList .ch").forEach((e) => e.classList.toggle("on", e._it === it));
    }
  }
  if (S.view === "fav") renderFav();
  if (S.view === "movie") renderItems("movie");
  if (S.view === "multi") mvStart();
  syncLive();
};
window.bergaBack = function() {
  if (oskOpen()) {
    oskClose(false);
    return true;
  }
  if (document.fullscreenElement) {
    document.exitFullscreen().catch(() => {
    });
    return true;
  }
  if (!$("#modal").classList.contains("hidden")) {
    closeModal();
    return true;
  }
  if (vodOpen()) {
    closeVod();
    return true;
  }
  const a = document.activeElement;
  if (a && a.id === "q") {
    a.blur();
    if (S.q) {
      a.value = "";
      a.dispatchEvent(new Event("input"));
    }
    return true;
  }
  if (S.view !== "live") {
    setView("live");
    if (TV) setTimeout(() => {
      const b = $("#nav [data-view=live]");
      b && b.focus();
    }, 50);
    return true;
  }
  if (WEBOS) {
    try {
      if (window.PalmSystem && PalmSystem.platformBack) {
        PalmSystem.platformBack();
        return true;
      }
    } catch (e) {
    }
    window.close();
    return true;
  }
  return false;
};
window.bergaAppPause = function() {
  S.appPaused = true;
  syncLive();
  mvStop();
};
window.bergaAppResume = function() {
  S.appPaused = false;
  if (!S.nativeOpen) {
    syncLive();
    if (S.view === "multi") mvStart();
  }
};
function spatial(dir) {
  const cur = document.activeElement && document.activeElement !== document.body ? document.activeElement : null;
  const root = oskOpen() ? $("#osk") : !$("#modal").classList.contains("hidden") ? $("#modal") : document;
  const els = [...root.querySelectorAll('button,input,select,[tabindex]:not([tabindex="-1"])')].filter((e) => {
    if (e.disabled || e.offsetParent === null) return false;
    const r = e.getBoundingClientRect();
    return r.width > 0 && r.height > 0 && !e.closest(".hidden") && !(root === document && (e.closest("#modal") || e.closest("#osk")));
  });
  if (!cur || !els.includes(cur)) {
    const f = els.find((e) => e.matches(".ch.on")) || els.find((e) => e.matches("#nav .on")) || els[0];
    if (f) {
      f.focus();
      f.scrollIntoView({ block: "nearest" });
    }
    return;
  }
  const c = cur.getBoundingClientRect(), cx = c.left + c.width / 2, cy = c.top + c.height / 2;
  let best = null, bs = 1e12;
  for (const e of els) {
    if (e === cur || e.contains(cur)) continue;
    const r = e.getBoundingClientRect(), dx = r.left + r.width / 2 - cx, dy = r.top + r.height / 2 - cy;
    let main, cross;
    if (dir === "ArrowRight") {
      if (r.left < c.right - 6 || r.bottom < c.top + 2 || r.top > c.bottom - 2) continue;
      main = r.left - c.right;
      cross = Math.abs(dy);
    } else if (dir === "ArrowLeft") {
      if (r.right > c.left + 6 || r.bottom < c.top + 2 || r.top > c.bottom - 2) continue;
      main = c.left - r.right;
      cross = Math.abs(dy);
    } else if (dir === "ArrowDown") {
      if (r.top < c.bottom - 6) continue;
      main = r.top - c.bottom;
      cross = Math.max(0, Math.abs(dx) - (r.width + c.width) / 2);
    } else {
      if (r.bottom > c.top + 6) continue;
      main = c.top - r.bottom;
      cross = Math.max(0, Math.abs(dx) - (r.width + c.width) / 2);
    }
    const sc = Math.max(0, main) + cross * 3;
    if (sc < bs) {
      bs = sc;
      best = e;
    }
  }
  if (best) {
    best.focus({ preventScroll: true });
    best.scrollIntoView({ block: "nearest", inline: "nearest" });
  }
}
if (TV) document.documentElement.classList.add("tv");
if (AND) document.documentElement.classList.add("android");
if (WEBOS) document.documentElement.classList.add("webos");
function goLive() {
  const v = $("#liveVideo"), e = engines.get(v);
  if (!S.cur) return;
  if (e && e.hls && isFinite(e.hls.liveSyncPosition) && e.hls.liveSyncPosition > 0 && v.readyState >= 2) {
    v.currentTime = e.hls.liveSyncPosition;
    const pl = v.play();
    pl && pl.catch && pl.catch(() => {
    });
    toast("Ao vivo");
  } else {
    S.liveOn = true;
    startLive(S.cur);
    placePlayer();
    toast("Reconectando no ao vivo…");
  }
}
const two = (n) => String(n).padStart(2, "0");
function cuUrl(it, start, durMin) {
  const d = new Date((start + (S.acct && S.acct.tzOff || 0)) * 1e3);
  const ts = `${d.getUTCFullYear()}-${two(d.getUTCMonth() + 1)}-${two(d.getUTCDate())}:${two(d.getUTCHours())}-${two(d.getUTCMinutes())}`;
  return `${S.x.base}/timeshift/${enc(S.x.u)}/${enc(S.x.p)}/${Math.max(1, Math.ceil(durMin))}/${ts}/${it.xid}.ts`;
}
const dayLbl = (t) => {
  const d = new Date(t * 1e3), n = /* @__PURE__ */ new Date(), y = new Date(Date.now() - 864e5);
  if (d.toDateString() === n.toDateString()) return "Hoje";
  if (d.toDateString() === y.toDateString()) return "Ontem";
  return d.toLocaleDateString("pt-BR", { weekday: "long", day: "2-digit", month: "2-digit" });
};
function playCatchup(it, p) {
  const dur = (p[1] - p[0]) / 60;
  playVod({ k: "cu|" + it.k + "|" + p[0], name: `${it.name} · ${p[2]} (${dayLbl(p[0])} ${hhmm(p[0])})`, logo: it.logo, url: cuUrl(it, p[0], dur) });
}
function openArchive(it) {
  return __async(this, null, function* () {
    S.modalFor = "arch";
    const draw = (html) => modal(`<button class="mx" data-close>✕</button><h2>⏪ ${esc(it.name)}</h2><p class="muted small">Programas que já passaram e ficam guardados pelo seu provedor por ${it.arch} dia${it.arch > 1 ? "s" : ""}.</p>${html}`);
    draw('<p class="muted">Carregando programação anterior…</p>');
    let list = [];
    try {
      const j = JSON.parse(yield txt(xapi("get_simple_data_table", "&stream_id=" + it.xid)));
      const b64 = (s) => {
        try {
          return new TextDecoder().decode(Uint8Array.from(atob(s || ""), (c) => c.charCodeAt(0)));
        } catch (e) {
          return s || "";
        }
      };
      const nt = nowS(), lim = nt - it.arch * 86400;
      list = arr(j.epg_listings).map((e) => [+e.start_timestamp, +e.stop_timestamp, b64(e.title), b64(e.description), +e.has_archive]).filter((p) => p[0] && p[1] <= nt && p[0] >= lim && (p[4] || p[4] === 0 ? true : true)).sort((a, b) => b[0] - a[0]);
    } catch (e) {
      if (S.modalFor === "arch") draw('<p class="muted">Não consegui carregar: ' + esc(e.message) + "</p>");
      return;
    }
    if (S.modalFor !== "arch") return;
    if (!list.length) return draw('<p class="muted">O provedor não informou programas anteriores para este canal.</p>');
    let h = "", lastDay = "";
    list.forEach((p, i) => {
      const dl = dayLbl(p[0]);
      if (dl !== lastDay) {
        h += `<div class="arcDay">${esc(dl)}</div>`;
        lastDay = dl;
      }
      h += `<div class="arcRow" tabindex="0" data-i="${i}"><span class="t">${hhmm(p[0])}</span><span>${esc(p[2])}</span><span class="d">${Math.round((p[1] - p[0]) / 60)} min</span></div>`;
    });
    draw(h);
    $("#modalCard").onclick = (e) => {
      const r = e.target.closest(".arcRow");
      if (!r) return;
      closeModal();
      playCatchup(it, list[+r.dataset.i]);
    };
    if (TV) setTimeout(() => {
      const r = document.querySelector(".arcRow");
      r && r.focus();
    }, 60);
  });
}
function progModal(it, p) {
  const nt = nowS(), past = p[1] <= nt, live = p[0] <= nt && nt < p[1], canCu = S.x && it.arch && p[0] >= nt - it.arch * 86400, rb = recBase(), hasRb = rb != null, rm = recMark(it, p);
  S.modalFor = "prog";
  const btns = [];
  if (live) btns.push('<button class="btn pri" data-p="watch">▶ Assistir agora</button>');
  if (past && canCu) btns.push('<button class="btn pri" data-p="cu">▶ Assistir</button>');
  if (live && canCu) btns.push('<button class="btn" data-p="cu">⏮ Assistir do início</button>');
  if (!past) btns.push(rm ? `<button class="btn" data-p="unrec">⏹ Cancelar gravação</button>` : `<button class="btn${live ? "" : " pri"}" data-p="rec">⏺ Gravar${live ? " a partir de agora" : ""}</button>`);
  if (!live && !past) btns.push('<button class="btn" data-p="watch">Ir para o canal</button>');
  modal(`<button class="mx" data-close>✕</button><p class="muted small" style="margin:0">${esc(it.name)} · ${esc(dayLbl(p[0]))} ${hhmm(p[0])} – ${hhmm(p[1])}</p><h2 style="margin-top:6px">${esc(p[2] || "Sem título")}</h2>${p[3] ? `<p class="muted">${esc(p[3])}</p>` : ""}${past && !canCu ? '<p class="muted small">Este programa já passou e o canal não tem programas anteriores no seu provedor.</p>' : ""}${!past && !hasRb ? `<p class="muted small">${AND || WEBOS ? "Para gravar, informe em ⚙ Configurações o endereço do computador com o Berga TV aberto pelo atalho “rede Wi-Fi”." : ""}</p>` : ""}<div class="mBtns">${btns.join("")}</div>`);
  $("#modalCard").onclick = (e) => __async(this, null, function* () {
    const b = e.target.closest("[data-p]");
    if (!b) return;
    const a = b.dataset.p;
    if (a === "watch") {
      closeModal();
      setView("live");
      playLive(it);
      return;
    }
    if (a === "cu") {
      closeModal();
      playCatchup(it, p);
      return;
    }
    if (a === "rec") {
      if (!hasRb) {
        toast(AND || WEBOS ? "Informe o endereço do computador em ⚙ Configurações para gravar." : "Gravação indisponível.", true);
        return;
      }
      b.disabled = true;
      yield recAdd(it, p);
      closeModal();
      return;
    }
    if (a === "unrec") {
      const r = REC.items.find((x) => x.k === recKey(it, p));
      if (r) {
        try {
          yield recPost("/dl/act", { id: r.id, act: r.status === "gravando" ? "stop" : "stop" });
          toast("Gravação cancelada");
        } catch (err) {
          toast("Erro: " + err.message, true);
        }
        yield recFetch();
      }
      closeModal();
      return;
    }
  });
  if (TV) setTimeout(() => {
    const b = document.querySelector("#modalCard .mBtns .btn");
    b && b.focus();
  }, 60);
}
const REC = { items: [], ok: null, sig: "", timer: null };
function normPc(v) {
  v = String(v || "").trim().replace(/\/+$/, "");
  if (!v) return "";
  if (!/^https?:\/\//i.test(v)) v = "http://" + v;
  if (!/:\d+$/.test(v.replace(/^https?:\/\//, ""))) v += ":8765";
  return v;
}
function recBase() {
  if (AND || WEBOS) return S.cfg.pcAddr || null;
  return location.protocol.indexOf("http") === 0 ? "" : null;
}
const recKey = (it, p) => "rec|" + it.k + "|" + p[0];
const recMark = (it, p) => REC.items.some((x) => x.k === recKey(it, p) && (x.status === "agendado" || x.status === "gravando"));
function recPost(path, body) {
  return __async(this, null, function* () {
    const b = recBase();
    if (b == null) throw new Error("sem computador configurado");
    const r = yield fetch(b + path, { method: "POST", headers: { "Content-Type": "text/plain" }, body: JSON.stringify(body || {}) });
    const j = yield r.json().catch(() => ({}));
    if (!r.ok || j.erro) throw new Error(j.erro || "HTTP " + r.status);
    return j;
  });
}
function recUrl(it) {
  return S.x ? it.url.replace(/\.m3u8(\?|$)/, ".ts$1") : it.url;
}
function recAdd(it, p) {
  return __async(this, null, function* () {
    const d = new Date(p[0] * 1e3), nm = `${p[2] || "Programa"} - ${it.name} - ${two(d.getDate())}-${two(d.getMonth() + 1)} ${two(d.getHours())}h${two(d.getMinutes())}`;
    try {
      const j = yield recPost("/dl/add", { ua: S.cfg.ua, items: [{ kind: "rec", k: recKey(it, p), name: `${p[2] || "Programa"} · ${it.name}`, channel: it.name, prog: p[2] || "", logo: it.logo || "", url: recUrl(it), start: Math.max(p[0], Math.floor(nowS())), end: p[1], folder: ["Gravações"], filename: nm }] });
      toast(j.added ? `⏺ Gravação agendada: ${p[2]} (${hhmm(p[0])}). O computador precisa estar ligado com o Berga TV aberto.` : "Essa gravação já estava agendada.");
      yield recFetch();
      if (S.view === "guide") renderGuide();
      renderLiveInfo();
    } catch (e) {
      toast("Não consegui agendar no computador: " + e.message + (AND || WEBOS ? " (confira o endereço em ⚙ e se o atalho “rede Wi-Fi” está aberto no PC)" : ""), true);
    }
  });
}
function recFetch() {
  return __async(this, null, function* () {
    const b = recBase();
    if (b == null) {
      REC.ok = null;
      REC.items = [];
    } else {
      try {
        const r = yield fetch(b + "/dl/list", { cache: "no-store" });
        const j = yield r.json();
        REC.items = (j.items || []).filter((x) => x.kind === "rec");
        REC.ok = true;
      } catch (e) {
        REC.ok = false;
      }
    }
    const n = REC.items.filter((x) => x.status === "gravando").length, bd = $("#recBadge");
    bd.textContent = n ? "●" : "";
    bd.style.display = n ? "inline-block" : "none";
    if (S.view === "rec") renderRec();
    clearTimeout(REC.timer);
    REC.timer = setTimeout(recFetch, S.view === "rec" ? 3e3 : 6e4);
  });
}
function renderRec(force) {
  const box = $("#recBox"), b = recBase();
  const sig = REC.ok + "|" + b + "|" + REC.items.map((x) => x.id + x.status + (x.exists ? 1 : 0)).join(",");
  if (!force && sig === REC.sig) {
    REC.items.forEach((d) => {
      const r = box.querySelector(`.dlRow[data-id="${d.id}"] .dlSt`);
      if (r) r.textContent = recTxt(d);
    });
    return;
  }
  REC.sig = sig;
  if (b == null) {
    box.innerHTML = `<h3>Gravações</h3><p>Quem grava é o <b>computador</b>: ele precisa estar ligado com o Berga TV aberto pelo atalho <b>“Berga TV (rede Wi-Fi)”</b>. A TV e o celular podem ficar desligados.</p><p class="muted">Para agendar por aqui, informe em ⚙ Configurações o endereço que aparece na janela preta do computador (ex.: 192.168.1.24:8765).</p><button class="btn pri" data-r="cfg">Abrir configurações</button>`;
    return;
  }
  if (REC.ok === false) {
    box.innerHTML = `<h3>Gravações</h3><p class="dlSt err">Não consegui falar com o computador${b ? " (" + esc(b) + ")" : ""}. Ele está ligado e com o Berga TV aberto${AND || WEBOS ? " pelo atalho “rede Wi-Fi”" : ""}?</p><button class="btn" data-r="retry">Tentar de novo</button>${AND || WEBOS ? ' <button class="btn" data-r="cfg">Alterar endereço</button>' : ""}`;
    return;
  }
  const sch = REC.items.filter((x) => x.status === "agendado").sort((a, c) => a.start - c.start), run = REC.items.filter((x) => x.status === "gravando" || x.status === "parado"), done = REC.items.filter((x) => x.status === "concluido" || x.status === "erro").sort((a, c) => (c.finished || c.end) - (a.finished || a.end));
  const row = (d) => `<div class="dlRow" data-id="${d.id}"><img ${d.logo ? `src="${esc(d.logo)}"` : ""} alt=""><div class="dlMain"><b>${esc(d.name)}</b><div class="dlSt${d.status === "erro" ? " err" : ""}">${esc(recTxt(d))}</div></div><div class="dlBtns">${d.status === "agendado" ? `<button class="btn sm danger" data-r="stop" data-id="${d.id}">Cancelar</button>` : d.status === "gravando" ? `<button class="btn sm danger" data-r="stop" data-id="${d.id}">⏹ Parar</button>` : (d.exists ? `<button class="btn sm pri" data-r="play" data-id="${d.id}">▶ Assistir</button>` : "") + `<button class="btn sm danger" data-r="delete" data-id="${d.id}">Apagar</button>`}</div></div>`;
  box.innerHTML = `<p class="muted small" style="margin:0 2px 14px">Agende pelo <b>Guia</b> ou pela lista “A seguir” do canal. Quem grava é o computador${b ? " (" + esc(b) + ")" : ""}: ele precisa estar ligado na hora do programa. Cada gravação usa uma conexão do seu plano enquanto grava.</p>` + (run.length ? "<h3>Gravando agora</h3>" + run.map(row).join("") : "") + (sch.length ? "<h3>Agendadas</h3>" + sch.map(row).join("") : "") + (done.length ? "<h3>Gravadas</h3>" + done.map(row).join("") : "") + (!REC.items.length ? '<p class="muted">Nenhuma gravação ainda. Abra o <b>Guia</b>, escolha um programa e toque em <b>⏺ Gravar</b>.</p>' : "");
}
function recTxt(d) {
  const dt = (t) => dayLbl(t) + " " + hhmm(t);
  if (d.status === "agendado") return `${dt(d.start)} – ${hhmm(d.end)} · agendada`;
  if (d.status === "gravando") return `● Gravando até ${hhmm(d.end)} · ${fmtB(d.done)}${d.msg ? " · " + d.msg : ""}`;
  if (d.status === "parado") return "Finalizando…";
  if (d.status === "erro") return "Não gravou: " + (d.msg || "erro");
  return `${dt(d.start)} · ${fmtB(d.total || d.done)}${d.msg ? " · " + d.msg : ""}${d.exists ? "" : " · arquivo não encontrado"}`;
}
$("#recBox").onclick = (e) => __async(this, null, function* () {
  const b = e.target.closest("[data-r]");
  if (!b) return;
  const a = b.dataset.r, id = b.dataset.id, d = REC.items.find((x) => x.id === id);
  if (a === "cfg") {
    openSettings();
    setTimeout(() => {
      const i = document.querySelector("#cfgForm [name=pcAddr]");
      i && (i.scrollIntoView({ block: "center" }), i.focus());
    }, 60);
    return;
  }
  if (a === "retry") {
    REC.sig = "";
    recFetch();
    return;
  }
  if (a === "play" && d) {
    const base = recBase() || "";
    const url = base ? base + "/dl/file/" + d.id + d.ext : "/dl/file/" + d.id + d.ext;
    playVod({ k: "rec|" + d.id, name: d.name, logo: d.logo, url });
    return;
  }
  if (a === "delete" && !confirm('Apagar a gravação "' + (d ? d.name : "") + '" do computador?')) return;
  try {
    b.disabled = true;
    yield recPost("/dl/act", { id, act: a });
    REC.sig = "";
    yield recFetch();
  } catch (err) {
    toast("Erro: " + err.message, true);
  }
});
const OSKON = WEBOS || TVBROWSER;
const OSK = { el: null, target: null, shift: false };
const oskOpen = () => !$("#osk").classList.contains("hidden");
function oskIsText(e) {
  return e && e.tagName === "INPUT" && /^(text|password|search|url|email|)$/i.test(e.type || "");
}
function oskShow(inp) {
  OSK.target = inp;
  OSK.val = inp.value;
  OSK.shift = false;
  oskRender();
  $("#osk").classList.remove("hidden");
  setTimeout(() => {
    const b = document.querySelector('#osk button[data-k="a"]') || document.querySelector("#osk button");
    b && b.focus();
  }, 30);
}
function oskRender() {
  const sh = OSK.shift, L = (k) => sh && k.length === 1 ? k.toUpperCase() : k;
  const rows = [["1", "2", "3", "4", "5", "6", "7", "8", "9", "0"], ["q", "w", "e", "r", "t", "y", "u", "i", "o", "p"], ["a", "s", "d", "f", "g", "h", "j", "k", "l", "@"], ["z", "x", "c", "v", "b", "n", "m", ".", "-", "_"], ["http://", "https://", ".com", ":", "/", "?", "=", "&"]];
  const lbl = OSK.target && OSK.target.closest("label") ? OSK.target.closest("label").firstChild.textContent.trim() : OSK.target && OSK.target.placeholder || "Digite";
  $("#osk").innerHTML = `<div class="oskTop"><span class="oskLbl">${esc(lbl)}</span><div class="oskVal">${esc(OSK.val)}</div></div>` + rows.map((r) => `<div class="oskRow">${r.map((k) => `<button type="button" data-k="${esc(k)}" class="${k.length > 3 ? "w2" : ""}">${esc(L(k))}</button>`).join("")}</div>`).join("") + `<div class="oskRow"><button type="button" data-k="#shift" class="w2">${sh ? "abc" : "ABC"}</button><button type="button" data-k=" " class="w4">espaço</button><button type="button" data-k="#bs" class="w2">⌫ Apagar</button><button type="button" data-k="#clr" class="w2">Limpar</button><button type="button" data-k="#ok" class="w2 ok">✓ OK</button></div>`;
}
function oskSetVal() {
  $("#osk .oskVal").textContent = OSK.val;
}
function oskClose(apply) {
  const t = OSK.target;
  $("#osk").classList.add("hidden");
  OSK.target = null;
  if (t) {
    if (apply) {
      t.value = OSK.val;
      t.dispatchEvent(new Event("input", { bubbles: true }));
      t.dispatchEvent(new Event("change", { bubbles: true }));
    }
    try {
      t.focus({ preventScroll: true });
    } catch (e) {
      t.focus();
    }
  }
}
$("#osk").addEventListener("click", (e) => {
  const b = e.target.closest("button");
  if (!b) return;
  const k = b.dataset.k;
  if (k === "#ok") return oskClose(true);
  if (k === "#bs") {
    OSK.val = OSK.val.slice(0, -1);
    return oskSetVal();
  }
  if (k === "#clr") {
    OSK.val = "";
    return oskSetVal();
  }
  if (k === "#shift") {
    OSK.shift = !OSK.shift;
    const i = [...document.querySelectorAll("#osk button")].indexOf(b);
    oskRender();
    const nb = document.querySelectorAll("#osk button")[i];
    nb && nb.focus();
    return;
  }
  OSK.val += OSK.shift && k.length === 1 ? k.toUpperCase() : k;
  oskSetVal();
});
if (OSKON) document.addEventListener("click", (e) => {
  if (oskIsText(e.target) && !oskOpen()) {
    e.preventDefault();
    oskShow(e.target);
  }
}, true);
const UPD = { manual: false, info: null };
function appVer() {
  try {
    return JSON.parse(AND.appVersion());
  } catch (e) {
    return { code: 0, name: "?" };
  }
}
function updCheck(manual) {
  if (!AND || !AND.checkUpdate) return;
  UPD.manual = manual;
  if (manual) {
    const e = $("#updSt");
    e && (e.textContent = "Verificando…");
  }
  AND.checkUpdate();
}
window.onUpdateInfo = function(j) {
  try {
    j = JSON.parse(j);
  } catch (e) {
    return;
  }
  UPD.info = j;
  LS.set("updAt", Date.now());
  const st = $("#updSt");
  if (j.erro) {
    if (st) st.textContent = "Não consegui verificar: " + j.erro;
    if (UPD.manual) toast("Não consegui verificar atualização: " + j.erro, true);
    return;
  }
  const has = j.latest > j.current && j.url;
  if (st) st.textContent = has ? `Nova versão ${j.name} disponível.` : `Você está na versão mais recente (${j.currentName}).`;
  if (!has) {
    if (UPD.manual && !st) toast("Você já está na versão mais recente.");
    return;
  }
  if (!UPD.manual && LS.get("updSkip", 0) === j.latest) return;
  updModal(j);
};
function updModal(j) {
  S.modalFor = "upd";
  modal(`<button class="mx" data-close>✕</button><h2>Nova versão disponível</h2><p class="muted">Berga TV ${esc(j.name)} (você está na ${esc(j.currentName)}).</p>${j.notes ? `<p class="small muted" style="white-space:pre-line">${esc(j.notes).slice(0, 600)}</p>` : ""}<div id="updBox"></div><div class="mBtns"><button class="btn pri" data-u="go">⬇ Atualizar agora</button><button class="btn" data-u="later">Depois</button></div><p class="muted small" style="margin-top:14px">Suas listas, favoritos e downloads continuam depois de atualizar.</p>`);
  $("#modalCard").onclick = (e) => {
    const b = e.target.closest("[data-u]");
    if (!b) return;
    if (b.dataset.u === "later") {
      LS.set("updSkip", j.latest);
      closeModal();
      return;
    }
    $("#updBox").innerHTML = '<div class="bar big"><i style="width:0%"></i></div><p class="small muted" id="updMsg">Iniciando download…</p>';
    b.disabled = true;
    AND.installUpdate(j.url);
  };
  if (TV) setTimeout(() => {
    const b = document.querySelector("[data-u=go]");
    b && b.focus();
  }, 60);
}
window.onUpdateProgress = function(j) {
  try {
    j = JSON.parse(j);
  } catch (e) {
    return;
  }
  const m = $("#updMsg"), bar = document.querySelector("#updBox .bar i"), go = document.querySelector("[data-u=go]");
  if (j.perm) {
    if (m) m.textContent = "";
    const box = $("#updBox");
    if (box) box.innerHTML = '<p class="small">Na tela que abriu, ative <b>"Permitir desta fonte"</b> para o Berga TV, volte e toque em <b>Atualizar agora</b> de novo. (Só na primeira vez.)</p>';
    if (go) go.disabled = false;
    return;
  }
  if (j.erro) {
    if (m) m.textContent = "Erro: " + j.erro;
    if (go) go.disabled = false;
    return;
  }
  if (j.done) {
    if (m) m.textContent = "Download concluído. Confirme a instalação na tela do Android.";
    if (bar) bar.style.width = "100%";
    if (go) go.disabled = false;
    return;
  }
  if (bar && j.pct >= 0) bar.style.width = j.pct + "%";
  if (m) m.textContent = j.pct >= 0 ? `Baixando… ${j.pct}%` : "Baixando…";
};
function devModeReminder() {
  const now = Date.now(), D = 864e5;
  let last = LS.get("devRenewAt", 0);
  if (!last) {
    LS.set("devRenewAt", now);
    return;
  }
  if (now - last < 30 * D || now < LS.get("devRemindAt", 0) || !$("#modal").classList.contains("hidden")) return;
  const left = Math.max(0, 41 - Math.floor((now - last) / D));
  S.modalFor = "devmode";
  modal(`<button class="mx" data-close>✕</button><h2>Renove o modo desenvolvedor</h2><p>O modo desenvolvedor desta TV vence em <b>cerca de ${left} dias</b>. Se vencer, o Berga TV é removido da TV e precisa ser instalado de novo.</p><p class="muted">Para renovar (leva 10 segundos): no computador, abra o <b>webOS Dev Manager</b> → aba <b>Info</b> → <b>Renew session</b>. Ou, na TV, abra o app <b>Developer Mode</b> e clique em <b>Extend</b>.</p><div class="mBtns"><button class="btn pri" data-dm="ok">Já renovei</button><button class="btn" data-dm="later">Lembrar em 3 dias</button></div>`);
  $("#modalCard").onclick = (e) => {
    const b = e.target.closest("[data-dm]");
    if (!b) return;
    if (b.dataset.dm === "ok") {
      LS.set("devRenewAt", Date.now());
      toast("Ótimo! Aviso de novo daqui a 30 dias.");
    } else LS.set("devRemindAt", Date.now() + 3 * D);
    closeModal();
  };
  setTimeout(() => {
    const b = document.querySelector("[data-dm=ok]");
    b && b.focus();
  }, 60);
}
function webosUpdCheck() {
  fetch("https://api.github.com/repos/rodrigobergaa/berga-tv-app/releases/latest").then((r) => r.json()).then((j) => {
    LS.set("updAt", Date.now());
    const cur = +String(window.BERGA_VERSION || "0").split(".").pop(), tag = String(j.tag_name || ""), lat = +tag.split(".").pop();
    if (!(lat > cur) || LS.get("updSkip", 0) === lat) return;
    S.modalFor = "upd";
    modal(`<button class="mx" data-close>✕</button><h2>Nova versão disponível</h2><p class="muted">Berga TV ${esc(tag.replace(/^v/, ""))} (esta TV está na ${esc(window.BERGA_VERSION || "?")}).</p><p>Para atualizar, abra o <b>webOS Dev Manager</b> no computador e instale o arquivo <b>BergaTV.ipk</b> novo por cima. Suas listas e favoritos continuam.</p><div class="mBtns"><button class="btn pri" data-close>Ok</button><button class="btn" data-skip>Não avisar desta versão</button></div>`);
    $("#modalCard").onclick = (e) => {
      if (e.target.closest("[data-skip]")) {
        LS.set("updSkip", lat);
        closeModal();
      }
    };
    setTimeout(() => {
      const b = document.querySelector("#modalCard .btn.pri");
      b && b.focus();
    }, 60);
  }).catch(() => {
  });
}
(function init() {
  setView(["live", "guide", "movie", "series", "multi", "fav", "dl", "rec"].includes(S.view) && !(WEBOS && ["multi", "dl"].includes(S.view)) ? S.view : "live");
  dlFetch();
  recFetch();
  if (!window.Hls || !window.mpegts) toast("Não consegui carregar os componentes de vídeo (precisa de internet). Alguns canais podem não abrir.", true);
  window.__bergaOk = true;
  loadActive(false);
  if (TV) setTimeout(() => {
    const b = $("#nav button.on");
    b && b.focus();
  }, 400);
  if (AND && Date.now() - LS.get("updAt", 0) > 6 * 36e5) setTimeout(() => updCheck(false), 5e3);
  if (WEBOS && Date.now() - LS.get("updAt", 0) > 6 * 36e5) setTimeout(webosUpdCheck, 8e3);
  if (WEBOS) setTimeout(devModeReminder, 3e3);
})();
</script>
</body>
</html>
'''

if __name__ == "__main__":
    main()
