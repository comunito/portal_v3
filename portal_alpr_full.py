from __future__ import annotations
from flask import Flask, jsonify, render_template_string, Response, request, redirect, url_for, send_file
import cv2, threading, time, os, json, csv, requests, subprocess, re, datetime, base64, queue, glob
# Forzar a OpenCV FFmpeg a usar transporte TCP, deshabilitar buffers y minimizar la latencia de inicio
os.environ["OPENCV_FFMPEG_CAPTURE_OPTIONS"] = "rtsp_transport;tcp|max_delay;100000|analyzeduration;100000|probesize;100000|fflags;nobuffer|flags;low_delay"
import numpy as np
from collections import OrderedDict
from copy import deepcopy
from io import StringIO
from zoneinfo import ZoneInfo
import socket
from urllib.parse import urlparse
import ipaddress
import sys
import traceback

script_dir = os.path.dirname(os.path.abspath(__file__))
LOG_FILE = os.path.join(script_dir, "portal_history.csv")
CRASH_LOG = os.path.join(script_dir, "crash.log")
thread_heartbeats = {}

def _iso_now_early():
    try:
        tz = globals().get("TZ")
        if tz:
            return datetime.datetime.now(tz=tz).isoformat()
    except Exception:
        pass
    return datetime.datetime.now().isoformat()

def crash_handler(etype, value, tb):
    try:
        with open(CRASH_LOG, "a", encoding="utf-8") as f:
            f.write(f"\n--- CRASH AT {_iso_now_early()} ---\n")
            traceback.print_exception(etype, value, tb, file=f)
            f.flush()
            os.fsync(f.fileno())
    except Exception:
        pass
    sys.__excepthook__(etype, value, tb)

sys.excepthook = crash_handler


# Limitar hilos de librerías matemáticas ANTES de que cualquier thread los herede
os.environ.setdefault("OMP_NUM_THREADS", "2")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "2")

try:
    import serial
except Exception:
    serial = None

# =========================
#  Comunito Portal FULL v6.7.6
#  - SIN bitácora (eliminada)
#  - Webhooks: 2 por estado (Activo/Inactivo/NoFound) para Placas (owners+visitors)
#  - Tags: solo owners (activo/inactivo) + NoFound (2 webhooks)
#  - Snapshot por endpoint (multipart o json b64)
#  - Snapshot NO se captura si no hay endpoint con snapshot activo
#  - Colas acotadas (drop controlado) para evitar saturación y congelamientos
#  - Gate: HTTP o SERIAL/USB autodetect (sin depender de IP)
# =========================

TZ = ZoneInfo("America/Mexico_City")
CFG_FILE = "config_full.json"
APP_TITLE = "Comunito Pi — ALPR FULL (2 cámaras, v6.7.6)"

# ---------- Utils ----------
def _clampi(v, lo, hi, fb):
    try: v=int(float(v))
    except: return fb
    return max(lo, min(hi, v))

def _clampf(v, lo, hi, fb):
    try: v=float(v)
    except: return fb
    return max(lo, min(hi, v))

def canon_plate(s: str) -> str:
    return "".join([c for c in str(s or "").upper() if c.isalnum()])

def _safe(row, one_based_idx):
    if one_based_idx is None: return ""
    i=int(one_based_idx)-1
    return (row[i].strip() if (row and 0<=i<len(row) and row[i]) else "")

def _norm_url(u: str) -> str:
    """
    Normaliza URL base para Gate HTTP.
    - Acepta hostname sin esquema: gate-esp32.local, pluma-cam1
    - Fuerza http:// si no hay esquema
    - Quita trailing /
    - Si el usuario pegó .../pulse, lo convierte a base (para no duplicar /pulse/pulse)
    """
    u=(u or "").strip()
    if not u: return ""
    if not (u.startswith("http://") or u.startswith("https://")):
        u="http://"+u
    u=u.strip()

    # quitar trailing slashes
    while u.endswith("/") and len(u) > len("http://x"):
        u=u[:-1]

    # evitar /pulse duplicado si el usuario lo incluyó
    # (dejamos la base para que _gate_fire_http agregue /pulse una sola vez)
    if u.lower().endswith("/pulse"):
        u=u[:-len("/pulse")]
        while u.endswith("/") and len(u) > len("http://x"):
            u=u[:-1]
    return u

def _safe_key(s: str, fallback: str) -> str:
    import unicodedata
    s=(s or "").strip().lower()
    s=unicodedata.normalize('NFKD', s).encode('ascii','ignore').decode('ascii')
    out=[]; prev=False
    for ch in s:
        if ch.isalnum(): out.append(ch); prev=False
        else:
            if not prev: out.append('_'); prev=True
    k="".join(out).strip("_")
    return k or fallback

def _gs_url(s: str) -> str:
    s=(s or "").strip()
    if not s: return ""
    if "http" in s:
        if ("/export?" in s) and ("format=csv" in s): return s
        p=s.find("/d/")
        if p>=0:
            p+=3; q=s.find("/",p); sheet_id=s[p:q] if q>p else s[p:]
            return f"https://docs.google.com/spreadsheets/d/{sheet_id}/export?format=csv"
        return s
    return f"https://docs.google.com/spreadsheets/d/{s}/export?format=csv"

def col_to_idx(x, fb=None):
    if x is None: return fb
    s=str(x).strip()
    if s=="": return fb
    if re.fullmatch(r"\d+", s): return int(s)
    if re.fullmatch(r"[A-Za-z]+", s):
        s=s.upper(); n=0
        for ch in s: n = n*26 + (ord(ch)-64)
        return n
    return fb

def _norm_cols_any(v, n=3):
    out=[]
    try:
        for x in list(v)[:n]:
            if x is None or str(x).strip()=="":
                out.append(None)
            else:
                out.append(col_to_idx(x, None))
    except:
        return ([2,3,4] if n==3 else [2,3,4,5])
    while len(out)<n: out.append(None)
    return out

def _parse_bool_form(v)->bool:
    return str(v).lower() in ("1","true","t","yes","on","si","sí","checked")

# ---------- Defaults ----------
WH_PAIR_DEF = {
    "url1": "", "send_snapshot1": False, "snapshot_mode1": "multipart",
    "url2": "", "send_snapshot2": False, "snapshot_mode2": "multipart"
}

WL_DEF = {
    "sheets_input": "",
    "search_start_col": 14,
    "search_end_col": 18,
    "status_col": 3,
    "disp_cols": [2,3,4],
    "disp_titles": ["Folio","Nombre","Telefono"],
    "auto_refresh_min": 0,
    "wh_active":   deepcopy(WH_PAIR_DEF),
    "wh_inactive": deepcopy(WH_PAIR_DEF),
}

MOTION_DEF = {
    "enabled": True,
    "pixel_change_pct": 2.0,
    "intensity_delta": 25,
    "autobase_every_min": 10,
    "autobase_samples": 3,
    "autobase_interval_s": 1.0,
    "cooldown_s": 2.0
}

TAG_DEF = {
    "lookup_format": "physical",  # physical | internal_hex
    "owners": deepcopy(WL_DEF),
    "wh_notfound": deepcopy(WH_PAIR_DEF)
}

CAM_DEF = {
    "camera_mode": "mac",
    "camera_mac": "",
    "camera_url": "rtsp://usuario:pass@{CAM_IP}:554/Streaming/Channels/102",
    "process_every_n": 2,
    "resize_max_w": 1280,
    "alpr_topk": 3,
    "min_confidence": 0.90,
    "idle_clear_sec": 1.5,
    "det_min_confidence": 0.80,
    "stable_hits_required": 2,
    "notfound_stable_hits_required": 4,
    "suppress_notfound_after_auth_sec": 8,
    "latch_hold_sec": 1.0,

    # Pre-procesado (solo ALPR, NO afecta snapshot/stream)
    "pp_enabled": False,
    "pp_profile": "none",         # none | bw_hicontrast_sharp
    "pp_clahe_clip": 2.0,         # 1.0 - 4.0
    "pp_sharp_strength": 0.55,    # 0.0 - 1.2

    "owners": deepcopy(WL_DEF),
    "visitors": deepcopy(WL_DEF),
    "wh_notfound": deepcopy(WH_PAIR_DEF),

    "roi": {"enabled": False, "x": 0.0, "y": 0.0, "w": 1.0, "h": 1.0},
    "motion": deepcopy(MOTION_DEF),

    # Gate
    "gate_enabled": False,
    "gate_auto_on_auth": False,
    "gate_antispam_sec": 4,
    "gate_pulse_ms": 500,

    # Gate HTTP
    "gate_mode": "serial",          # "http" o "serial"
    "gate_url": "",
    "gate_token": "12345",
    "gate_pin": 5,
    "gate_active_low": False,

    # Gate SERIAL/USB
    "gate_serial_device": "",       # vacío = autodetect (/dev/serial/by-id/*)
    "gate_serial_baud": 115200,
    "gate_serial_gate": 1,          # 1 cam1, 2 cam2

    # Dedup/gap (aplica a ACTIVE/INACTIVE/NOTFOUND y tags)
    "wh_repeat_same_plate": False,
    "wh_min_gap_sec": 0,

    "tags": deepcopy(TAG_DEF),
}

DEFAULTS = {
    "cameras": [deepcopy(CAM_DEF), deepcopy(CAM_DEF)],
    "api_token": "",
    "monitor_enabled": False,
    "monitor_url": "",
    "monitor_period_min": 0
}

def load_cfg():
    d = deepcopy(DEFAULTS)
    if os.path.exists(CFG_FILE):
        try:
            with open(CFG_FILE,"r") as f:
                user = json.load(f) or {}
                if isinstance(user, dict):
                    d.update(user)
        except:
            pass

    cams = d.get("cameras", [])
    if not isinstance(cams, list) or len(cams) == 0:
        cams = [deepcopy(CAM_DEF), deepcopy(CAM_DEF)]
    while len(cams) < 2:
        cams.append(deepcopy(CAM_DEF))
    if len(cams) > 2:
        cams = cams[:2]

    for i,c in enumerate(cams, start=1):
        c["camera_mac"] = (c.get("camera_mac","") or "").upper().replace("-",":")
        c["camera_mode"] = ("manual" if (c.get("camera_mode","mac") or "mac").lower()=="manual" else "mac")

        c["process_every_n"] = _clampi(c.get("process_every_n",2),1,30,2)
        c["resize_max_w"] = _clampi(c.get("resize_max_w",1280),64,4096,1280)
        c["alpr_topk"] = _clampi(c.get("alpr_topk",3),1,5,3)
        c["min_confidence"] = _clampf(c.get("min_confidence",0.90),0.0,1.0,0.90)
        c["idle_clear_sec"] = max(0.5, float(c.get("idle_clear_sec",1.5)))
        c["det_min_confidence"] = _clampf(c.get("det_min_confidence",0.80),0.0,1.0,0.80)
        c["stable_hits_required"] = _clampi(c.get("stable_hits_required",2),1,5,2)
        c["notfound_stable_hits_required"] = _clampi(c.get("notfound_stable_hits_required",4),1,10,4)
        c["suppress_notfound_after_auth_sec"] = _clampi(c.get("suppress_notfound_after_auth_sec",8),0,60,8)
        c["latch_hold_sec"] = max(1.0, float(c.get("latch_hold_sec",1.0)))

        for sect in ("owners","visitors"):
            w = c.get(sect,{}) or {}
            wk = deepcopy(WL_DEF)
            wk["wh_active"]   = {**deepcopy(WH_PAIR_DEF), **(w.get("wh_active") or {})}
            wk["wh_inactive"] = {**deepcopy(WH_PAIR_DEF), **(w.get("wh_inactive") or {})}
            wk.update({k:v for k,v in w.items() if k not in ("wh_active","wh_inactive")})
            wk["search_start_col"] = col_to_idx(wk.get("search_start_col",14),14)
            wk["search_end_col"]   = col_to_idx(wk.get("search_end_col",18),18)
            if wk["search_end_col"] < wk["search_start_col"]:
                wk["search_end_col"] = wk["search_start_col"]
            wk["status_col"] = col_to_idx(wk.get("status_col",3),3)
            wk["auto_refresh_min"] = _clampi(wk.get("auto_refresh_min",0),0,1440,0)
            wk["disp_cols"] = _norm_cols_any(wk.get("disp_cols",[2,3,4]),3)
            if not isinstance(wk.get("disp_titles"), list) or len(wk["disp_titles"]) < 3:
                wk["disp_titles"] = ["Campo 1","Campo 2","Campo 3"]
            wk["disp_titles"] = list(wk["disp_titles"][:3]) + [""]*(3-len(wk["disp_titles"][:3]))
            c[sect] = wk

        c["wh_notfound"] = {**deepcopy(WH_PAIR_DEF), **(c.get("wh_notfound") or {})}

        c["roi"] = {**deepcopy(CAM_DEF["roi"]), **(c.get("roi") or {})}
        for k in ("x","y","w","h"):
            c["roi"][k] = float(c["roi"].get(k, CAM_DEF["roi"][k]))
        c["roi"]["enabled"] = bool(c["roi"].get("enabled", False))

        c["motion"] = {**deepcopy(MOTION_DEF), **(c.get("motion") or {})}
        c["motion"]["pixel_change_pct"] = float(c["motion"].get("pixel_change_pct", MOTION_DEF["pixel_change_pct"]))
        c["motion"]["intensity_delta"]  = _clampi(c["motion"].get("intensity_delta", MOTION_DEF["intensity_delta"]), 1, 255, MOTION_DEF["intensity_delta"])
        c["motion"]["autobase_every_min"] = _clampi(c["motion"].get("autobase_every_min", MOTION_DEF["autobase_every_min"]), 1, 1440, MOTION_DEF["autobase_every_min"])
        c["motion"]["autobase_samples"] = _clampi(c["motion"].get("autobase_samples", MOTION_DEF["autobase_samples"]), 1, 5, MOTION_DEF["autobase_samples"])
        c["motion"]["autobase_interval_s"] = max(0.2, float(c["motion"].get("autobase_interval_s", MOTION_DEF["autobase_interval_s"])))
        c["motion"]["cooldown_s"] = max(0.2, float(c["motion"].get("cooldown_s", MOTION_DEF["cooldown_s"])))
        c["motion"]["enabled"] = bool(c["motion"].get("enabled", True))

        # Gate
        c["gate_antispam_sec"] = _clampi(c.get("gate_antispam_sec",4),1,600,4)
        c["gate_pulse_ms"]     = _clampi(c.get("gate_pulse_ms",500),20,10000,500)
        c["gate_pin"]          = _clampi(c.get("gate_pin",5),1,39,5)
        c["gate_url"]          = _norm_url(c.get("gate_url",""))
        c["gate_mode"]         = (c.get("gate_mode","serial") or "serial").lower()
        if c["gate_mode"] not in ("http","serial"):
            c["gate_mode"]="serial"
        c["gate_serial_device"] = (c.get("gate_serial_device","") or "").strip()
        c["gate_serial_baud"]   = _clampi(c.get("gate_serial_baud",115200), 1200, 921600, 115200)
        c["gate_serial_gate"]   = _clampi(c.get("gate_serial_gate", i), 1, 8, i)

        c["wh_min_gap_sec"]    = _clampi(c.get("wh_min_gap_sec",0),0,3600,0)
        c["wh_repeat_same_plate"] = bool(c.get("wh_repeat_same_plate", False))

        # Tags
        t = c.get("tags",{}) or {}
        tt = deepcopy(TAG_DEF)
        tt["lookup_format"] = (t.get("lookup_format") or "physical")
        ow = t.get("owners",{}) or {}
        wk = deepcopy(WL_DEF)
        wk["wh_active"]   = {**deepcopy(WH_PAIR_DEF), **(ow.get("wh_active") or {})}
        wk["wh_inactive"] = {**deepcopy(WH_PAIR_DEF), **(ow.get("wh_inactive") or {})}
        wk.update({k:v for k,v in ow.items() if k not in ("wh_active","wh_inactive")})
        wk["search_start_col"] = col_to_idx(wk.get("search_start_col",14),14)
        wk["search_end_col"]   = col_to_idx(wk.get("search_end_col",18),18)
        if wk["search_end_col"] < wk["search_start_col"]:
            wk["search_end_col"] = wk["search_start_col"]
        wk["status_col"] = col_to_idx(wk.get("status_col",3),3)
        wk["auto_refresh_min"] = _clampi(wk.get("auto_refresh_min",0),0,1440,0)
        wk["disp_cols"] = _norm_cols_any(wk.get("disp_cols",[2,3,4]),3)
        if not isinstance(wk.get("disp_titles"), list) or len(wk["disp_titles"]) < 3:
            wk["disp_titles"] = ["Campo 1","Campo 2","Campo 3"]
        wk["disp_titles"] = list(wk["disp_titles"][:3]) + [""]*(3-len(wk["disp_titles"][:3]))
        tt["owners"] = wk
        tt["wh_notfound"] = {**deepcopy(WH_PAIR_DEF), **(t.get("wh_notfound") or {})}
        c["tags"] = tt

    d["cameras"] = cams
    d["monitor_enabled"] = bool(d.get("monitor_enabled", False))
    d["monitor_url"] = d.get("monitor_url","")
    d["monitor_period_min"] = _clampi(d.get("monitor_period_min",0),0,1440,0)
    return d

def save_cfg(c):
    with open(CFG_FILE,"w") as f:
        json.dump(c, f, indent=2)

cfg = load_cfg()

# ========== Gate Serial Manager ==========
class GateSerialManager:
    def __init__(self):
        self.lock = threading.Lock()
        self.ser = None
        self.device = ""
        self.baud = 115200
        self.last_ok = 0.0
        self.last_err = ""
        self.q = queue.Queue(maxsize=200)
        self.t = threading.Thread(target=self._loop, daemon=True)
        self.t.start()

    def _pick_device(self, preferred:str="") -> str:
        if preferred and os.path.exists(preferred):
            return preferred
        byid = sorted(glob.glob("/dev/serial/by-id/*"))
        for p in byid:
            if os.path.exists(p): return p
        for pat in ("/dev/ttyACM*", "/dev/ttyUSB*"):
            for p in sorted(glob.glob(pat)):
                if os.path.exists(p): return p
        return ""

    def _open(self, dev:str, baud:int):
        if serial is None:
            self.last_err="pyserial no disponible"
            return False
        try:
            s = serial.Serial(dev, baudrate=baud, timeout=0.15, write_timeout=0.5)
            try:
                s.reset_input_buffer()
                s.reset_output_buffer()
            except Exception:
                pass
            with self.lock:
                if self.ser:
                    try: self.ser.close()
                    except Exception: pass
                self.ser = s
                self.device = dev
                self.baud = baud
                self.last_ok = time.time()
                self.last_err = ""
            return True
        except Exception as e:
            self.last_err = str(e)
            return False

    def _close(self):
        with self.lock:
            if self.ser:
                try: self.ser.close()
                except Exception: pass
            self.ser=None

    def status(self):
        with self.lock:
            return {
                "connected": bool(self.ser),
                "device": self.device,
                "baud": self.baud,
                "last_ok": self.last_ok,
                "last_err": self.last_err,
                "pending": self.q.qsize()
            }

    def send_pulse(self, gate:int, ms:int):
        try:
            self.q.put_nowait({"cmd":"pulse","gate":int(gate),"ms":int(ms)})
            return True
        except queue.Full:
            return False

    def _loop(self):
        while True:
            thread_heartbeats["gate_serial"] = time.time()
            # Preferencia: si alguna cam define gate_serial_device, úsala
            preferred=""
            baud=115200
            for cam in (1,2):
                c=cfg["cameras"][cam-1]
                dev=(c.get("gate_serial_device","") or "").strip()
                if dev:
                    preferred=dev
                    baud=int(c.get("gate_serial_baud",115200))
                    break
                baud=int(c.get("gate_serial_baud",115200))

            with self.lock:
                alive = bool(self.ser)
                dev_current = self.device

            if not alive:
                dev = self._pick_device(preferred)
                if dev:
                    self._open(dev, baud)
                time.sleep(0.6)
                continue

            # Si cambió preferencia, reabrir
            if preferred and preferred != dev_current and os.path.exists(preferred):
                self._open(preferred, baud)
                time.sleep(0.2)

            # Drenar entrada
            try:
                with self.lock: s=self.ser
                if s:
                    try: _ = s.read(256)
                    except Exception: pass
            except Exception:
                pass

            # Enviar cola
            try:
                item = self.q.get(timeout=0.25)
            except queue.Empty:
                time.sleep(0.05)
                continue

            try:
                line = (json.dumps(item, separators=(",",":")) + "\n").encode("utf-8")
                with self.lock: s=self.ser
                if not s:
                    try: self.q.put_nowait(item)
                    except queue.Full: pass
                    time.sleep(0.2)
                else:
                    try:
                        s.write(line)
                        self.last_ok=time.time()
                    except Exception as e:
                        self.last_err=str(e)
                        self._close()
                        try: self.q.put_nowait(item)
                        except queue.Full: pass
                        time.sleep(0.4)
            finally:
                try: self.q.task_done()
                except Exception: pass

gate_serial = GateSerialManager()

# ========== MAC→IP ==========
MAC_RE=re.compile(r'^[0-9A-F]{2}(:[0-9A-F]{2}){5}$')
_ip_cache={"mac2ip":{}, "ts":0.0}

def resolve_ip_by_mac(mac:str, ttl=1.5)->str|None:
    mac=(mac or "").upper()
    now=time.time()
    if not MAC_RE.match(mac): return None
    if (now-_ip_cache["ts"])<ttl:
        ip=_ip_cache["mac2ip"].get(mac)
        if ip: return ip
    try:
        with open("/var/lib/misc/dnsmasq.leases","r") as f:
            for line in f:
                p=line.strip().split()
                if len(p)>=3 and p[1].upper()==mac:
                    ip=p[2].strip()
                    if ip:
                        _ip_cache["mac2ip"][mac]=ip; _ip_cache["ts"]=now
                        return ip
    except: pass
    try:
        with open("/proc/net/arp","r") as f:
            next(f)
            for ln in f:
                cols=ln.split()
                if len(cols)>=4 and cols[3].upper()==mac:
                    ip=cols[0]; _ip_cache["mac2ip"][mac]=ip; _ip_cache["ts"]=now; return ip
    except: pass
    return None

def materialize_url(cdict:dict):
    url=(cdict.get("camera_url","") or "").strip()
    mode=(cdict.get("camera_mode","mac") or "mac").lower()
    if (mode=="mac") and ("{CAM_IP}" in url):
        ip=resolve_ip_by_mac(cdict.get("camera_mac",""))
        if ip: return url.replace("{CAM_IP}", ip), ip, "LAN-MAC"
        return url, None, "LAN-MAC(PEND)"
    ip=None
    try: ip=url.split("@")[1].split(":")[0]
    except: ip=None
    return url, ip, "MANUAL"

def _ping(ip:str, timeout=1)->bool:
    if not ip: return False
    try:
        subprocess.check_output(["ping","-c","1","-W",str(timeout),ip], stderr=subprocess.DEVNULL)
        return True
    except:
        return False

# ========== RTSP LOW-LATENCY ==========
os.environ["OPENCV_FFMPEG_CAPTURE_OPTIONS"] = \
    "rtsp_transport;tcp|fflags;nobuffer|flags;low_delay|reorder_queue_size;0|max_delay;0|stimeout;3000000"

class VideoSource:
    def __init__(self, cidx:int):
        self.cidx=cidx
        self.lock=threading.Lock()
        self.frame=None
        self.ts=0.0
        self.running=False
        self.t=None
        self.last_ip=None

    def get(self):
        with self.lock:
            return self.frame

    def get_with_ts(self):
        with self.lock:
            return self.frame, self.ts

    def _open_cv(self, url): return cv2.VideoCapture(url)

    def _open_gst(self, url):
        if not url.lower().startswith("rtsp://"): return None
        pipeline = (
            f"rtspsrc location=\"{url}\" protocols=tcp latency=0 drop-on-latency=true ! "
            "rtph264depay ! h264parse ! avdec_h264 ! videoconvert ! "
            "appsink sync=false max-buffers=1 drop=true"
        )
        cap=cv2.VideoCapture(pipeline, cv2.CAP_GSTREAMER)
        if cap is not None and cap.isOpened(): return cap
        return None

    def start(self):
        if self.running: return
        self.running=True
        self.t=threading.Thread(target=self._loop, daemon=True)
        self.t.start()

    def _loop(self):
        try: cv2.setNumThreads(1)
        except: pass
        while self.running:
            c=cfg["cameras"][self.cidx]
            url, ip, _ = materialize_url(c)

            # Si sigue literal {CAM_IP}, no intentes abrir hasta resolver MAC->IP
            if "{CAM_IP}" in (url or ""):
                time.sleep(0.5)
                continue

            if ip: self.last_ip=ip
            if self.last_ip and not _ping(self.last_ip,1):
                time.sleep(0.5); continue
            cap=None
            try:
                cap = self._open_gst(url)
                if cap is not None and cap.isOpened():
                    print(f"[CAM{self.cidx+1}] Abierta con GStreamer (latencia 0)")
                else:
                    print(f"[CAM{self.cidx+1}] GStreamer no disponible. Usando OpenCV FFmpeg con fflags=nobuffer...")
                    cap = self._open_cv(url)
                if not cap or not cap.isOpened():
                    time.sleep(0.6); continue

                # ── Zero-Latency Buffer: entregar siempre el frame más reciente ──
                try:
                    cap.set(cv2.CAP_PROP_BUFFERSIZE, 1)
                except Exception:
                    pass

                last=time.time()
                while self.running:
                    ok, fr = cap.read()
                    thread_heartbeats[f"grab_cam{self.cidx+1}"] = time.time()
                    if not ok or fr is None: break

                    try:
                        mx=int(cfg["cameras"][self.cidx].get("resize_max_w",1280))
                        if mx and fr.shape[1] > mx:
                            h,w = fr.shape[:2]
                            tw=mx
                            th=int(max(36, h*(tw/float(w))))
                            fr=cv2.resize(fr, (tw,th), interpolation=cv2.INTER_AREA)
                    except:
                        pass

                    with self.lock:
                        self.frame=fr
                        self.ts=time.time()

                    if (time.time()-last)>2.0:
                        last=time.time()
                        url2, ip2, _ = materialize_url(c)
                        if ip2 and self.last_ip and ip2!=self.last_ip:
                            break
                    time.sleep(0.001)
            except Exception:
                pass
            finally:
                try:
                    if cap: cap.release()
                except: pass
            time.sleep(0.3)

grab=[VideoSource(0), VideoSource(1)]
for g in grab: g.start()

# ========== ALPR ==========
try:
    from fast_alpr import ALPR
    print("[ALPR] import fast_alpr OK")
    alpr = ALPR(
        detector_model="yolo-v9-t-384-license-plate-end2end",
        ocr_model="cct-xs-v1-global-model"
    )
    ALPR_OK = True
    print("[ALPR] engine OK")
except Exception as e:
    print("[ALPR] no disponible:", e)
    alpr = None
    ALPR_OK = False

def run_alpr(image_bgr, resize_max_w, topk=3):
    if not ALPR_OK or image_bgr is None:
        return []

    H0, W0 = image_bgr.shape[:2]
    if W0 < 2 or H0 < 2:
        return []

    def _best_conf(v):
        if v is None:
            return 0.0
        if isinstance(v, (int, float)):
            return float(v)
        if isinstance(v, (list, tuple)):
            vals = []
            for x in v:
                try:
                    vals.append(float(x))
                except Exception:
                    pass
            return max(vals) if vals else 0.0
        try:
            return float(v)
        except Exception:
            return 0.0

    img = image_bgr
    target_w = max(64, int(resize_max_w))
    if target_w < W0:
        scale = max(1e-6, float(target_w) / float(W0))
        try:
            img = cv2.resize(
                image_bgr,
                (max(64, int(W0 * scale)), max(36, int(H0 * scale))),
                interpolation=cv2.INTER_AREA
            )
        except Exception:
            img = image_bgr

    try:
        res = alpr.predict(img) or []
    except Exception as e:
        print("[ALPR] predict error:", e)
        return []

    out = []
    for r in res:
        det = getattr(r, "detection", None)
        ocr = getattr(r, "ocr", None)
        if det is None or ocr is None:
            continue

        det_conf = _best_conf(getattr(det, "confidence", None))
        if det_conf <= 0.0:
            det_conf = _best_conf(getattr(det, "score", None))

        raw_text = getattr(ocr, "text", "")
        raw_conf = getattr(ocr, "confidence", 0.0)

        if isinstance(raw_text, (list, tuple)):
            conf_list = raw_conf if isinstance(raw_conf, (list, tuple)) else [raw_conf] * len(raw_text)
            for t, c in zip(raw_text, conf_list):
                tt = str(t or "").strip().upper()
                cc = _best_conf(c)
                if tt:
                    out.append((tt, cc, det_conf))
            continue

        text = str(raw_text or "").strip().upper()
        conf = _best_conf(raw_conf)
        if text:
            out.append((text, conf, det_conf))

    out.sort(key=lambda x: (x[1], x[2]), reverse=True)
    return out[:max(1, topk)]



# ========== Pre-procesado (solo ALPR) ==========
def _preprocess_for_alpr(cam:int, frame_bgr):
    """
    Ligero y opcional.
    - Se aplica SOLO al frame que entra al ALPR.
    - NO afecta snapshots / stream.
    - Ajustable por cámara: CLAHE clip + sharpen strength
    """
    try:
        c = cfg["cameras"][cam-1]
        if not c.get("pp_enabled", False):
            return frame_bgr
        prof = (c.get("pp_profile","none") or "none").strip().lower()
        if prof == "none" or frame_bgr is None:
            return frame_bgr

        h, w = frame_bgr.shape[:2]
        if h < 20 or w < 20:
            return frame_bgr

        if prof == "adaptive_auto":
            # ── Fotómetro por software: decide automaticamente si hace falta boost ──
            try:
                g = cv2.cvtColor(frame_bgr, cv2.COLOR_BGR2GRAY)
            except Exception:
                g = frame_bgr if len(frame_bgr.shape)==2 else frame_bgr

            mean_lum = float(np.mean(g))

            if mean_lum < 80:  # Condición nocturna / tormentosa
                try:
                    g = cv2.bilateralFilter(g, 9, 75, 75)
                    table = np.array([((i / 255.0) ** (1.0 / 0.8)) * 255
                                      for i in np.arange(0, 256)]).astype("uint8")
                    g = cv2.LUT(g, table)
                    clahe = cv2.createCLAHE(clipLimit=3.0, tileGridSize=(8, 8))
                    g = clahe.apply(g)
                    blur = cv2.GaussianBlur(g, (0, 0), 2.0)
                    g = cv2.addWeighted(g, 1.5, blur, -0.5, 0)
                except Exception:
                    pass
            else:  # Condición diurna: sólo nitidez suave
                try:
                    clahe = cv2.createCLAHE(clipLimit=1.5, tileGridSize=(8, 8))
                    g = clahe.apply(g)
                    blur = cv2.GaussianBlur(g, (0, 0), 1.0)
                    g = cv2.addWeighted(g, 1.3, blur, -0.3, 0)
                except Exception:
                    pass

            try:
                return cv2.cvtColor(g, cv2.COLOR_GRAY2BGR)
            except Exception:
                return frame_bgr

        if prof == "darkfighter":
            try:
                g = cv2.cvtColor(frame_bgr, cv2.COLOR_BGR2GRAY)
            except Exception:
                g = frame_bgr
            try:
                g = cv2.bilateralFilter(g, 9, 75, 75)
                table = np.array([((i / 255.0) ** (1.0/0.8)) * 255 for i in np.arange(0, 256)]).astype("uint8")
                g = cv2.LUT(g, table)
                clahe = cv2.createCLAHE(clipLimit=3.0, tileGridSize=(8,8))
                g = clahe.apply(g)
                blur = cv2.GaussianBlur(g, (0,0), 2.0)
                g = cv2.addWeighted(g, 1.5, blur, -0.5, 0)
                return cv2.cvtColor(g, cv2.COLOR_GRAY2BGR)
            except Exception:
                pass

        if prof == "bw_hicontrast_sharp":
            clip = _clampf(c.get("pp_clahe_clip", 2.0), 1.0, 4.0, 2.0)
            sharp = _clampf(c.get("pp_sharp_strength", 0.55), 0.0, 1.2, 0.55)

            # 1) a gris
            try:
                g = cv2.cvtColor(frame_bgr, cv2.COLOR_BGR2GRAY)
            except Exception:
                g = frame_bgr

            # 2) CLAHE (contraste local)
            try:
                clahe = cv2.createCLAHE(clipLimit=float(clip), tileGridSize=(8,8))
                g = clahe.apply(g)
            except Exception:
                pass

            # 3) Unsharp mask (nitidez) - controlado por sharp
            # w1 = 1 + sharp ; w2 = -sharp
            try:
                if float(sharp) > 0.001:
                    blur = cv2.GaussianBlur(g, (0,0), 1.0)
                    w1 = 1.0 + float(sharp)
                    w2 = -float(sharp)
                    g = cv2.addWeighted(g, w1, blur, w2, 0)
            except Exception:
                pass

            # 4) volver a BGR (fast-alpr espera BGR)
            try:
                return cv2.cvtColor(g, cv2.COLOR_GRAY2BGR)
            except Exception:
                return frame_bgr

        return frame_bgr
    except Exception:
        return frame_bgr

# ========== Whitelists ==========
wl_index=[{"owners":{}, "visitors":{}}, {"owners":{}, "visitors":{}}]
tag_index=[{"owners":{}}, {"owners":{}}]
_last_wl=[{ "owners":0.0, "visitors":0.0 }, { "owners":0.0, "visitors":0.0 }]
_last_tag_wl=[{ "owners":0.0 }, { "owners":0.0 }]

def _guess_has_header(rows)->bool:
    if not rows: return False
    header=rows[0]
    header_join=" ".join((header or []))[:128].upper()
    if any(tok in header_join for tok in ("PLACA","PLATE","ESTATUS","STATUS","NOMBRE","FOLIO","TAG","PHYSICAL","INTERNAL")):
        return True
    return any(header)

def _parse_csv_text(txt:str):
    try:
        f = StringIO(txt)
        return list(csv.reader(f))
    except:
        return []

def _max_need_col(section:dict)->int:
    cols=[]
    cols.append(int(col_to_idx(section.get("search_start_col",14),14)))
    cols.append(int(col_to_idx(section.get("search_end_col",18),18)))
    cols.append(int(col_to_idx(section.get("status_col",3),3)))
    dc = section.get("disp_cols",[2,3,4]) or [2,3,4]
    for x in dc[:3]:
        if x is not None:
            cols.append(int(col_to_idx(x, 1)))
    return max(cols) if cols else 18

def _build_idx_from_rows(cam:int, kind:str, rows:list[list[str]])->str:
    idx = wl_index[cam-1][kind]
    idx.clear()

    c = cfg["cameras"][cam-1][kind]
    s=int(col_to_idx(c.get("search_start_col",14),14))-1
    e=int(col_to_idx(c.get("search_end_col",18),18))-1
    if e<s: e=s
    start=1 if _guess_has_header(rows) else 0
    max_need=_max_need_col(c)

    added=replaced=total=0
    for row in rows[start:]:
        total += 1
        if not row: continue
        if len(row) > max_need:
            row = row[:max_need]
        for j in range(s, e+1):
            if j < len(row):
                key=canon_plate(row[j] or "")
                if not key: continue
                if key in idx: replaced += 1
                else: added += 1
                idx[key]=row
    return f"Índice {kind} cam{cam}: {added} (+{replaced}) de {total} filas"

def _build_tag_idx_from_rows(cam:int, rows:list[list[str]])->str:
    idx = tag_index[cam-1]["owners"]
    idx.clear()

    c = cfg["cameras"][cam-1]["tags"]["owners"]
    s=int(col_to_idx(c.get("search_start_col",14),14))-1
    e=int(col_to_idx(c.get("search_end_col",18),18))-1
    if e<s: e=s
    start=1 if _guess_has_header(rows) else 0
    max_need=_max_need_col(c)

    added=replaced=total=0
    for row in rows[start:]:
        total += 1
        if not row: continue
        if len(row) > max_need:
            row = row[:max_need]
        for j in range(s, e+1):
            if j < len(row):
                key=canon_plate(row[j] or "")
                if not key: continue
                if key in idx: replaced += 1
                else: added += 1
                idx[key]=row
    return f"Índice TAG owners cam{cam}: {added} (+{replaced}) de {total} filas"

def _local_cache_path(cam:int, kind:str)->str:
    return os.path.join(script_dir, f"cache_wl_cam{cam}_{kind}.json")

def _local_tag_cache_path(cam:int)->str:
    return os.path.join(script_dir, f"cache_tag_wl_cam{cam}_owners.json")

def _load_wl_from_cache():
    for cam in (1,2):
        for kind in ("owners", "visitors"):
            cache_path = _local_cache_path(cam, kind)
            if os.path.exists(cache_path):
                try:
                    with open(cache_path, "r", encoding="utf-8") as f:
                        rows = json.load(f)
                    msg = _build_idx_from_rows(cam, kind, rows)
                    print(f"[CACHE LOAD] {msg} (desde caché local)")
                except Exception as e:
                    print(f"[CACHE LOAD ERROR] cam{cam} {kind}: {e}")
        # Tags
        cache_path = _local_tag_cache_path(cam)
        if os.path.exists(cache_path):
            try:
                with open(cache_path, "r", encoding="utf-8") as f:
                    rows = json.load(f)
                msg = _build_tag_idx_from_rows(cam, rows)
                print(f"[CACHE LOAD] {msg} (desde caché local)")
            except Exception as e:
                print(f"[CACHE LOAD ERROR] cam{cam} tags: {e}")

def download_wl(cam:int, kind:str)->str:
    c=cfg["cameras"][cam-1][kind]
    url=_gs_url(c.get("sheets_input",""))
    if not url: return f"❌ Configura '{kind}.sheets_input'"
    try:
        r=requests.get(url, timeout=25)
        if r.status_code!=200:
            msg = f"❌ HTTP {r.status_code} descargando CSV"
            print(f"[WHITELIST ERROR][cam{cam}] {kind}: {msg}")
            return msg
        rows=_parse_csv_text(r.text)
    except Exception as e:
        msg = f"❌ Error WL: {e}"
        print(f"[WHITELIST ERROR][cam{cam}] {kind}: {msg}")
        return msg
    msg=_build_idx_from_rows(cam,kind,rows)
    print(f"[WHITELIST][cam{cam}] {msg}")
    
    try:
        cache_path = _local_cache_path(cam, kind)
        with open(cache_path, "w", encoding="utf-8") as f:
            json.dump(rows, f)
    except Exception as ce:
        print(f"[CACHE WRITE ERROR] cam{cam} {kind}: {ce}")
        
    _last_wl[cam-1][kind]=time.time()
    return msg

def download_tag_wl(cam:int)->str:
    c=cfg["cameras"][cam-1]["tags"]["owners"]
    url=_gs_url(c.get("sheets_input",""))
    if not url: return f"❌ Configura 'tags.owners.sheets_input'"
    try:
        r=requests.get(url, timeout=25)
        if r.status_code!=200:
            msg = f"❌ HTTP {r.status_code} descargando CSV"
            print(f"[WHITELIST ERROR][cam{cam}] tags: {msg}")
            return msg
        rows=_parse_csv_text(r.text)
    except Exception as e:
        msg = f"❌ Error TAG WL: {e}"
        print(f"[WHITELIST ERROR][cam{cam}] tags: {msg}")
        return msg
    msg=_build_tag_idx_from_rows(cam,rows)
    print(f"[WHITELIST][cam{cam}] {msg}")
    
    try:
        cache_path = _local_tag_cache_path(cam)
        with open(cache_path, "w", encoding="utf-8") as f:
            json.dump(rows, f)
    except Exception as ce:
        print(f"[CACHE WRITE ERROR] cam{cam} tags: {ce}")
        
    _last_tag_wl[cam-1]["owners"]=time.time()
    return msg

def lookup_row(cam:int, plate:str):
    p=canon_plate(plate)
    ro=wl_index[cam-1]["owners"].get(p)
    if ro is not None: return "PROPIETARIO", ro
    rv=wl_index[cam-1]["visitors"].get(p)
    if rv is not None: return "VISITA", rv
    return "NONE", None

def lookup_tag_row(cam:int, tag_key:str):
    p=canon_plate(tag_key)
    ro=tag_index[cam-1]["owners"].get(p)
    if ro is not None: return "PROPIETARIO", ro
    return "NONE", None

def is_active_from_row(csection:dict, row)->bool:
    idx=int(col_to_idx(csection.get("status_col",3),3))-1
    val=(row[idx] if (row and 0<=idx<len(row)) else "") or ""
    v=str(val).strip().upper()
    v=re.sub(r'[^A-Z0-9ÁÉÍÓÚÑ ]+', ' ', v); v=re.sub(r'\s+', ' ', v).strip()
    if v.startswith("ACTIV") or v.startswith("ACTIVE") or v=="ACT": return True
    if v in ("1","SI","SÍ","YES","Y","TRUE","T","ON"): return True
    if v.isdigit() and v=="1": return True
    return False

def _payload_kv_from_titles(titles, values):
    out={}
    for i,(t,v) in enumerate(zip(titles, values), start=1):
        out[_safe_key(t, f"campo_{i}")] = v
    return out

def _extract_fields(row, cols):
    cols = cols or [2,3,4]
    c1,c2,c3 = (cols+[None,None,None])[:3]
    return [
        _safe(row, col_to_idx(c1, None)),
        _safe(row, col_to_idx(c2, None)),
        _safe(row, col_to_idx(c3, None)),
    ]

# ========== Gate ==========
_state_gate_last=[0.0,0.0]
def gate_can_fire(cam:int)->bool:
    antispam=max(1,int(cfg["cameras"][cam-1].get("gate_antispam_sec",4)))
    return (time.time()-_state_gate_last[cam-1])>=antispam

def _gate_fire_http(cam:int)->tuple[bool,str]:
    c=cfg["cameras"][cam-1]
    base=_norm_url(c.get("gate_url",""))
    token=(c.get("gate_token") or "").strip()
    if not base or not token: return False,"Config incompleta gate HTTP"
    if not gate_can_fire(cam): return False, f"Anti-spam {c.get('gate_antispam_sec',4)}s"

    # endpoint final (una sola vez)
    pulse_url = (base if base.lower().endswith("/pulse") else (base + "/pulse"))

    # intentar resolver host para dar error claro (requests igual fallaría)
    try:
        from urllib.parse import urlparse
        import socket
        h = (urlparse(pulse_url).hostname or "").strip()
        if h:
            socket.gethostbyname(h)  # si falla, cae al except
    except Exception as e:
        return False, f"No resuelve hostname (DNS/mDNS): {e}"

    params={
        "token": token,
        "pin": int(c.get("gate_pin",5)),  # ✅ pin por cámara (cam1/cam2)
        "active_low": (1 if c.get("gate_active_low",False) else 0),
        "ms": int(c.get("gate_pulse_ms",500)),
        "cam": cam
    }

    # 2 intentos cortos para robustez sin colgar la app
    last_err=""
    for _ in range(2):
        try:
            r=requests.post(pulse_url, data=params, timeout=4)
            if r.status_code==200:
                _state_gate_last[cam-1]=time.time()
                return True,"OK"
            # fallback GET si firmware lo soporta
            r2=requests.get(pulse_url, params=params, timeout=4)
            if r2.status_code==200:
                _state_gate_last[cam-1]=time.time()
                return True,"OK"
            last_err=f"ESP32 HTTP {r.status_code}/{r2.status_code}"
        except Exception as e:
            last_err=f"ESP32 HTTP error: {e}"
        time.sleep(0.2)

    return False,last_err or "ESP32 HTTP fail"

def _gate_fire_serial(cam:int)->tuple[bool,str]:
    if serial is None:
        return False,"pyserial no disponible"
    if not gate_can_fire(cam): return False, f"Anti-spam {cfg['cameras'][cam-1].get('gate_antispam_sec',4)}s"
    c=cfg["cameras"][cam-1]
    gate_num=int(c.get("gate_serial_gate", cam))
    ms=int(c.get("gate_pulse_ms",500))
    ok=gate_serial.send_pulse(gate_num, ms)
    if not ok:
        return False,"Cola serial llena (drop)"
    _state_gate_last[cam-1]=time.time()
    st=gate_serial.status()
    if not st["connected"]:
        return False, "Serial no conectado (reintentando): " + (st.get("last_err","") or "")
    return True,"OK"

def gate_fire(cam:int)->tuple[bool,str]:
    c=cfg["cameras"][cam-1]
    if not c.get("gate_enabled",False): return False,"Gate deshabilitado"
    mode=(c.get("gate_mode","serial") or "serial").lower()
    if mode=="http":
        return _gate_fire_http(cam)
    return _gate_fire_serial(cam)

# ========== Dedup / envío (cola acotada) ==========
_last_sent_val=[{"ACTIVE":"","INACTIVE":"","NOTFOUND":""},{"ACTIVE":"","INACTIVE":"","NOTFOUND":""}]
_last_sent_ts =[{"ACTIVE":0.0,"INACTIVE":0.0,"NOTFOUND":0.0},{"ACTIVE":0.0,"INACTIVE":0.0,"NOTFOUND":0.0}]
_send_lock=[threading.Lock(), threading.Lock()]

def _jpeg_bytes(frame, q:int):
    ok,buf=cv2.imencode(".jpg", frame, [cv2.IMWRITE_JPEG_QUALITY, q])
    if not ok: return None
    return bytes(buf.tobytes())

class SendManager:
    def __init__(self, cam:int, max_q:int=80):
        self.cam=cam
        self.q=queue.Queue(maxsize=max_q)
        self.dropped=0
        self.sent=0
        self.t=threading.Thread(target=self._loop, daemon=True)
        self.t.start()

    def put(self, item:dict):
        try:
            self.q.put_nowait(item)
        except queue.Full:
            self.dropped += 1

    def _send_to_endpoint(self, sess:requests.Session, url, payload, snap_bytes, mode):
        url=(url or "").strip()
        if not url: return False, "no-url"
        mode_lower = (mode or "multipart").lower().strip()
        try:
            if snap_bytes is not None:
                if mode_lower == "json":
                    js=dict(payload)
                    js["snapshot_b64"]=base64.b64encode(snap_bytes).decode("ascii")
                    r=sess.post(url, json=js, timeout=8)
                else:
                    files={"snapshot": ("snapshot.jpg", snap_bytes, "image/jpeg")}
                    r=sess.post(url, data=payload, files=files, timeout=8)
            else:
                if mode_lower == "json":
                    r=sess.post(url, json=payload, timeout=8)
                else:
                    r=sess.post(url, data=payload, timeout=8)
            return (200 <= r.status_code < 400), f"HTTP {r.status_code}"
        except Exception as e:
            return False, str(e)

    def _loop(self):
        sess=requests.Session()
        while True:
            try:
                item=self.q.get(timeout=2.0)
            except queue.Empty:
                thread_heartbeats[f"send_mgr_cam{self.cam}"] = time.time()
                continue
            thread_heartbeats[f"send_mgr_cam{self.cam}"] = time.time()
            try:
                endpoints=item["endpoints"]
                payload=item["payload"]

                # Snapshot solo si algún endpoint lo pide (si no, NO capturamos frame)
                need_snap = any(bool(es) for (_,es,_) in endpoints)
                snap_jpeg=None
                if need_snap:
                    fr = grab[self.cam-1].get()
                    if fr is not None:
                        snap_jpeg = _jpeg_bytes(fr, 75)

                any_ok=False
                for url, send_snap, mode in endpoints:
                    if not (url or "").strip():
                        continue
                    snap = (snap_jpeg if (send_snap and snap_jpeg is not None) else None)
                    ok, err_msg = self._send_to_endpoint(sess, url, payload, snap, mode)
                    if ok:
                        print(f"[WEBHOOK][cam{self.cam}] Webhook enviado con éxito a {url} (Resp: {err_msg})")
                        any_ok = True
                    else:
                        print(f"[WEBHOOK ERROR][cam{self.cam}] Error al enviar webhook a {url}: {err_msg}")
                if any_ok:
                    self.sent += 1
            finally:
                self.q.task_done()

send_mgr=[SendManager(1), SendManager(2)]

def _should_send(cam:int, cat:str, value:str)->bool:
    cdict=cfg["cameras"][cam-1]
    key=canon_plate(value)
    if not key: return False
    now=time.time()
    last_k=canon_plate(_last_sent_val[cam-1].get(cat,""))
    last_t=float(_last_sent_ts[cam-1].get(cat,0.0))
    gap=max(0, int(cdict.get("wh_min_gap_sec",0)))
    allow_rep=bool(cdict.get("wh_repeat_same_plate",False))
    if not allow_rep:
        return key != last_k
    if key != last_k:
        return True
    return (gap<=0) or ((now-last_t) >= gap)

def _mark_sent(cam:int, cat:str, value:str):
    _last_sent_val[cam-1][cat]=canon_plate(value)
    _last_sent_ts[cam-1][cat]=time.time()

def _base_payload(cam:int, usuario:str, dispositivo:str, valor:str, disp_vals:list[str], titles:list[str]):
    payload = OrderedDict()
    payload["cam"] = cam
    payload["usuario"] = usuario
    payload["dispositivo"] = dispositivo
    payload["valor"] = canon_plate(valor)
    d1,d2,d3 = (disp_vals+["","",""])[:3]
    payload["disp_col_1"] = d1
    payload["disp_col_2"] = d2
    payload["disp_col_3"] = d3
    payload.update(_payload_kv_from_titles(titles, disp_vals))
    return payload

def _endpoints_pair(pair:dict):
    return [
        (pair.get("url1",""), bool(pair.get("send_snapshot1",False)), (pair.get("snapshot_mode1","multipart") or "multipart")),
        (pair.get("url2",""), bool(pair.get("send_snapshot2",False)), (pair.get("snapshot_mode2","multipart") or "multipart")),
    ]

def enqueue_webhooks(cam:int, cat:str, pair:dict, usuario:str, dispositivo:str, valor:str, disp_vals:list[str], titles:list[str]):
    endpoints=_endpoints_pair(pair or {})
    if not any((u or "").strip() for (u,_,_) in endpoints):
        return False, "Sin webhooks"
    with _send_lock[cam-1]:
        if not _should_send(cam, cat, valor):
            return False, "Dedup/gap"
        _mark_sent(cam, cat, valor)
    payload=_base_payload(cam, usuario, dispositivo, valor, disp_vals, titles)
    send_mgr[cam-1].put({"payload": dict(payload), "endpoints": endpoints})
    return True, "Encolado"

# ========== Motion + ROI ==========
class MotionState:
    def __init__(self):
        self.bg_subtractor=None
        self.active=False
        self.last_motion_ts=0.0
        self.trigger=threading.Event()
        self.last_ratio=0.0
        self.last_frame_ts=0.0

motion=[MotionState(), MotionState()]

def _apply_roi(cam:int, frame):
    roi=cfg["cameras"][cam-1].get("roi",{"enabled":False})
    if not roi.get("enabled"): return frame
    H,W=frame.shape[:2]
    x=max(0.0,min(1.0,float(roi.get("x",0.0))))
    y=max(0.0,min(1.0,float(roi.get("y",0.0))))
    w=max(0.0,min(1.0,float(roi.get("w",1.0))))
    h=max(0.0,min(1.0,float(roi.get("h",1.0))))
    if w<=0 or h<=0: return frame
    x0=int(round(x*W)); y0=int(round(y*H))
    x1=int(round((x+w)*W)); y1=int(round((y+h)*H))
    x0=max(0,min(W-1,x0)); x1=max(1,min(W,x1))
    y0=max(0,min(H-1,y0)); y1=max(1,min(H,y1))
    if x1-x0<8 or y1-y0<8: return frame
    return frame[y0:y1, x0:x1]

def _roi_gray_small(cam:int, frame):
    fr=_apply_roi(cam, frame)
    if fr is None: return None
    try: g=cv2.cvtColor(fr, cv2.COLOR_BGR2GRAY)
    except: g=fr
    h,w=g.shape[:2]
    if w>0:
        tw=min(320, w)
        if tw<w:
            th=int(max(32, h*(tw/float(w))))
            g=cv2.resize(g, (tw, th), interpolation=cv2.INTER_AREA)
    return g

def _motion_ratio(cam:int, gray)->float:
    st=motion[cam-1]
    if st.bg_subtractor is None:
        thr=int(cfg["cameras"][cam-1]["motion"].get("intensity_delta",25))
        st.bg_subtractor = cv2.createBackgroundSubtractorMOG2(history=300, varThreshold=thr, detectShadows=False)
    
    fg_mask = st.bg_subtractor.apply(gray)
    total = fg_mask.size
    if total == 0: return 0.0
    
    changed = int(np.count_nonzero(fg_mask > 127))
    return (100.0 * changed / float(total))

def _motion_loop(cam:int):
    c=cfg["cameras"][cam-1]["motion"]
    cooldown=float(max(0.2, c.get("cooldown_s",2.0)))
    last_check=0.0
    while True:
        thread_heartbeats[f"motion_cam{cam}"] = time.time()
        try:
            if not cfg["cameras"][cam-1]["motion"].get("enabled",True):
                motion[cam-1].active=True; time.sleep(0.2); continue
            
            fr, ts = grab[cam-1].get_with_ts()
            if fr is None or ts == motion[cam-1].last_frame_ts:
                time.sleep(0.02); continue
            
            motion[cam-1].last_frame_ts = ts
            now=time.time()
            
            if now - last_check < 0.05: time.sleep(0.02); continue
            last_check=now
            
            g=_roi_gray_small(cam, fr)
            if g is None: time.sleep(0.02); continue
            
            ratio=_motion_ratio(cam, g)
            motion[cam-1].last_ratio=ratio
            umbral=float(cfg["cameras"][cam-1]["motion"].get("pixel_change_pct",2.0))
            prev_active=motion[cam-1].active
            
            if ratio >= umbral:
                motion[cam-1].active=True; motion[cam-1].last_motion_ts=now
                if not prev_active: motion[cam-1].trigger.set()
            else:
                if (now - motion[cam-1].last_motion_ts) >= cooldown:
                    motion[cam-1].active=False
            
            time.sleep(0.02)
        except Exception as e:
            print(f"[_motion_loop][cam{cam}] error: {e}")
            time.sleep(0.2)

# ========== Auto-refresh WL ==========
def _auto_refresh_loop():
    for cam in (1,2):
        for kind in ("owners","visitors"):
            if (cfg["cameras"][cam-1][kind].get("sheets_input") or "").strip():
                download_wl(cam,kind)
        if (cfg["cameras"][cam-1]["tags"]["owners"].get("sheets_input") or "").strip():
            download_tag_wl(cam)
    while True:
        try:
            now=time.time()
            for cam in (1,2):
                for kind in ("owners","visitors"):
                    mins=int(cfg["cameras"][cam-1][kind].get("auto_refresh_min",0))
                    if mins>0 and (now - _last_wl[cam-1][kind]) >= (mins*60):
                        download_wl(cam,kind)
                tmins=int(cfg["cameras"][cam-1]["tags"]["owners"].get("auto_refresh_min",0))
                if tmins>0 and (now - _last_tag_wl[cam-1]["owners"]) >= (tmins*60):
                    download_tag_wl(cam)
        except Exception:
            pass
        time.sleep(3)

# ========== Sys monitor (temp/cpu) ==========
sys_status={"temp_c":None, "cpu_pct":0.0}
_cpu_prev=(0,0)

def _read_cpu_times():
    try:
        with open("/proc/stat","r") as f: ln=f.readline()
        parts=ln.split()
        if parts[0]!="cpu": return None
        vals=list(map(int, parts[1:8])); idle=vals[3]+vals[4]; total=sum(vals)
        return idle,total
    except: return None

def _read_temp_c():
    base="/sys/class/thermal"
    try:
        zones=[os.path.join(base,x,"temp") for x in os.listdir(base) if x.startswith("thermal_zone")]
        for p in zones:
            try:
                with open(p,"r") as f: raw=f.read().strip()
                if not raw: continue
                v=float(raw)
                if v>200: v/=1000.0
                if v<0: continue
                return round(v,1)
            except: continue
    except: pass
    try:
        out=subprocess.check_output(["vcgencmd","measure_temp"], text=True).strip()
        m=re.search(r"temp=([0-9.]+)'C", out)
        if m: return float(m.group(1))
    except: pass
    return None

def _sysmon_loop():
    global _cpu_prev
    t=_read_cpu_times()
    if t: _cpu_prev=t
    while True:
        t2=_read_cpu_times(); cpu_pct=0.0
        if t2 and _cpu_prev:
            idle0,tot0=_cpu_prev; idle1,tot1=t2
            di=idle1-idle0; dt=tot1-tot0
            if dt>0: cpu_pct=max(0.0, min(100.0, (1.0 - (di/float(dt)))*100.0))
            _cpu_prev=t2
        sys_status["cpu_pct"]=round(cpu_pct,1)
        sys_status["temp_c"]=_read_temp_c()
        time.sleep(1.0)


# ========== Heartbeat (monitor) ==========
hb_status = {
    "last_try_ts": 0.0,
    "last_ok_ts": 0.0,
    "last_code": None,
    "last_err": "",
    "sent": 0,
    "fail": 0,
    "dropped": 0,
    "pending": 0,
}

def _iso_now():
    try:
        return datetime.datetime.now(tz=TZ).isoformat()
    except Exception:
        return datetime.datetime.now().isoformat()

def log_event(event_type, cam, identifier, confidence, category, user_type, auth, display_vals):
    import csv
    row = [
        _iso_now(),
        event_type,
        f"CAM{cam}",
        identifier,
        f"{confidence:.2f}" if isinstance(confidence, float) else str(confidence),
        category,
        user_type,
        "AUTORIZADO" if auth else "DENEGADO",
        ";".join(display_vals)
    ]
    try:
        exists = os.path.exists(LOG_FILE)
        with open(LOG_FILE, "a", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            if not exists:
                writer.writerow(["Fecha/Hora", "Tipo", "Cámara", "Identificador", "Confianza", "Categoría", "Tipo Usuario", "Autorización", "Detalles"])
            writer.writerow(row)
            f.flush()
            os.fsync(f.fileno())
    except Exception as e:
        print("[LOG ERROR] No se pudo escribir en el log local:", e)

def _safe_hostname():
    try:
        return os.uname().nodename
    except Exception:
        try:
            import socket
            return socket.gethostname()
        except Exception:
            return ""

def _heartbeat_payload():
    # Estado real: cámaras/colas/temp/cpu/gate + último status por cam
    payload = OrderedDict()
    payload["ts"] = _iso_now()
    payload["app"] = APP_TITLE
    payload["host"] = _safe_hostname()

    # Net básico
    try:
        _, ipout = sh("hostname -I | awk '{print $1}' || true")
        payload["ip"] = (ipout or "").strip()
    except Exception:
        payload["ip"] = ""

    # Sys
    payload["temp_c"] = sys_status.get("temp_c")
    payload["cpu_pct"] = sys_status.get("cpu_pct")

    # Gate serial
    try:
        payload["gate_serial"] = gate_serial.status()
    except Exception:
        payload["gate_serial"] = {}

    # Por cámara
    cams=[]
    for cam in (1,2):
        c = cfg["cameras"][cam-1]
        camd = OrderedDict()
        camd["cam"] = cam

        # LAN (status real basado en URL materializada)
        try:
            url, mip, mmode = materialize_url(c)
            ip = None
            ok = False
            # Si la URL tiene una IP explícita, probamos ping/tcp
            if "{CAM_IP}" not in (url or ""):
                if mip:
                    ip = mip
                else:
                    # Extraer IP de la URL a la brava
                    try: ip = url.split("@")[1].split(":")[0]
                    except Exception: ip = None
                
                if ip:
                    # check TCP 554
                    try:
                        with socket.create_connection((ip, 554), timeout=0.6):
                            ok = True
                    except Exception:
                        ok = _ping(ip, 1)
            
            camd["lan_ok"] = bool(ok)
            camd["lan_ip"] = (ip or "")
        except Exception:
            camd["lan_ok"] = False
            camd["lan_ip"] = ""

        # Motion
        try:
            st = motion[cam-1]
            camd["motion_active"] = bool(st.active)
            camd["motion_ratio"] = float(getattr(st,"last_ratio",0.0) or 0.0)
        except Exception:
            camd["motion_active"] = False
            camd["motion_ratio"] = 0.0

        # Colas send_mgr
        try:
            q = send_mgr[cam-1].q
            camd["queue_pending"] = int(q.qsize())
            camd["queue_dropped"] = int(send_mgr[cam-1].dropped)
            camd["queue_sent"] = int(send_mgr[cam-1].sent)
        except Exception:
            camd["queue_pending"] = 0
            camd["queue_dropped"] = 0
            camd["queue_sent"] = 0

        # Último estado placa/tag (real)
        try:
            with slock[cam-1]:
                st = states[cam-1].copy()
                tg = tag_states[cam-1].copy()
            camd["plate"] = st.get("plate","")
            camd["plate_cat"] = st.get("cat","")
            camd["plate_user_type"] = st.get("user_type","")
            camd["plate_ts"] = st.get("ts",0.0)
            camd["tag"] = tg.get("tag","")
            camd["tag_cat"] = tg.get("cat","")
            camd["tag_user_type"] = tg.get("user_type","")
            camd["tag_ts"] = tg.get("ts",0.0)
        except Exception:
            pass

        cams.append(camd)

    payload["cameras"] = cams
    return payload

class HeartbeatManager:
    """
    Loop dedicado, no bloquea la app:
    - Queue acotada (drop controlado)
    - Reintentos con backoff corto
    """
    def __init__(self, max_q:int=20):
        self.q = queue.Queue(maxsize=max_q)
        self.t = threading.Thread(target=self._loop, daemon=True)
        self.t.start()

    def enqueue(self, reason:str="periodic"):
        try:
            self.q.put_nowait({"reason": reason, "ts": time.time()})
        except queue.Full:
            hb_status["dropped"] = int(hb_status.get("dropped",0)) + 1

    def _post_with_retries(self, sess:requests.Session, url:str, js:dict):
        # 3 intentos: 0.5s, 1s, 2s backoff
        last_err=""
        last_code=None
        for i,slp in enumerate((0.0, 0.5, 1.0, 2.0)):
            if slp>0: time.sleep(slp)
            try:
                r = sess.post(url, json=js, timeout=8)
                last_code = r.status_code
                if r.status_code == 200:
                    return True, r.status_code, ""
                last_err = f"HTTP {r.status_code}"
            except Exception as e:
                last_err = str(e)
        return False, last_code, last_err

    def _loop(self):
        sess = requests.Session()
        while True:
            try:
                try:
                    item = self.q.get(timeout=2.0)
                except queue.Empty:
                    thread_heartbeats["heartbeat_sender"] = time.time()
                    continue
                thread_heartbeats["heartbeat_sender"] = time.time()
                try:
                    hb_status["pending"] = int(self.q.qsize())
                    # Solo si está habilitado + URL + periodo >0 o si es "manual"
                    enabled = bool(cfg.get("monitor_enabled", False))
                    url = (cfg.get("monitor_url","") or "").strip()
                    period = int(cfg.get("monitor_period_min",0) or 0)
                    reason = (item.get("reason") or "periodic")

                    if (not enabled) or (not url):
                        # si no está habilitado, no enviamos (pero consumimos cola)
                        hb_status["last_err"] = "Monitor deshabilitado o sin URL"
                        continue

                    # Si es periódico y periodo==0, no envía
                    if reason == "periodic" and period <= 0:
                        hb_status["last_err"] = "Periodo=0 (off)"
                        continue

                    hb_status["last_try_ts"] = time.time()
                    payload = _heartbeat_payload()
                    payload["reason"] = reason

                    ok, code, err = self._post_with_retries(sess, url, payload)
                    hb_status["last_code"] = code
                    if ok:
                        hb_status["last_ok_ts"] = time.time()
                        hb_status["last_err"] = ""
                        hb_status["sent"] = int(hb_status.get("sent",0)) + 1
                    else:
                        hb_status["last_err"] = err or "fail"
                        hb_status["fail"] = int(hb_status.get("fail",0)) + 1
                finally:
                    try: self.q.task_done()
                    except Exception: pass
            except Exception:
                time.sleep(0.2)

heartbeat_mgr = HeartbeatManager()

def _heartbeat_scheduler_loop():
    # Scheduler liviano: cada 1s revisa si toca enviar
    last_sent=0.0
    while True:
        try:
            enabled = bool(cfg.get("monitor_enabled", False))
            url = (cfg.get("monitor_url","") or "").strip()
            period = int(cfg.get("monitor_period_min",0) or 0)
            if enabled and url and period>0:
                now=time.time()
                if (now - last_sent) >= (period*60.0):
                    heartbeat_mgr.enqueue("periodic")
                    last_sent = now
        except Exception:
            pass
        time.sleep(1.0)


# ========== Detección loops ==========
states=[{"plate":"", "conf":0.0, "ts":0.0, "display":["","",""], "titles":["Folio","Nombre","Telefono"], "auth":False, "cat":"NONE", "user_type":"NONE"},
        {"plate":"", "conf":0.0, "ts":0.0, "display":["","",""], "titles":["Folio","Nombre","Telefono"], "auth":False, "cat":"NONE", "user_type":"NONE"}]
tag_states=[{"tag":"", "ts":0.0, "auth":False, "cat":"NONE", "user_type":"NONE", "fields":["","",""]},
            {"tag":"", "ts":0.0, "auth":False, "cat":"NONE", "user_type":"NONE", "fields":["","",""]}]
slock=[threading.Lock(), threading.Lock()]
_stable_state=[{"last":"","hits":0},{"last":"","hits":0}]
_last_auth_ts=[0.0,0.0]

def _alpr_loop(cam:int):
    k=0
    last_frame_ts=0.0
    while True:
        thread_heartbeats[f"alpr_cam{cam}"] = time.time()
        try:
            cdict=cfg["cameras"][cam-1]
            mot=motion[cam-1]

            # 1. Verificar si hay movimiento antes de hacer cualquier cosa (evitamos consumir CPU)
            if cdict["motion"].get("enabled", True) and not mot.active:
                time.sleep(0.15)
                if mot.trigger.is_set():
                    mot.trigger.clear()
                else:
                    continue

            # 2. Control de salteo de frames
            # Si se acaba de activar el movimiento, procesamos el primer frame de inmediato (k=0)
            if mot.trigger.is_set():
                mot.trigger.clear()
                k = 0
            else:
                k = (k + 1) % cdict["process_every_n"]
                if k != 0:
                    time.sleep(0.01)
                    continue

            # 3. Obtener el frame más RECIENTE posible justo antes de la inferencia IA
            fr, ts = grab[cam-1].get_with_ts()
            if fr is None or ts == last_frame_ts:
                time.sleep(0.01)
                continue
            last_frame_ts = ts

            fr_roi=_apply_roi(cam, fr)
            fr_alpr=_preprocess_for_alpr(cam, fr_roi)

            try:
                results=run_alpr(fr_alpr, cdict["resize_max_w"], topk=cdict["alpr_topk"])
            except Exception as e:
                print(f"[ALPR][cam{cam}] run_alpr fatal:", e)
                time.sleep(0.2)
                continue

            if not results:
                _stable_state[cam-1]["last"]=""
                _stable_state[cam-1]["hits"]=0
                time.sleep(0.1)
                continue

            text, conf, det_conf = results[0]

            if det_conf < float(cdict.get("det_min_confidence", 0.80)):
                _stable_state[cam-1]["last"] = ""
                _stable_state[cam-1]["hits"] = 0
                time.sleep(0.05)
                continue

            min_conf = float(cdict.get("min_confidence", 0.85))
            if conf < min_conf:
                _stable_state[cam-1]["last"] = ""
                _stable_state[cam-1]["hits"] = 0
                time.sleep(0.05)
                continue

            key = canon_plate(text)
            
            # --- CONSULTA PREVIA DE WHITELIST PARA RESPUESTA INMEDIATA (AGILIZACIÓN) ---
            # Para placas que ya están en la lista y autorizadas, disparamos en el PRIMER hit
            # Para placas no encontradas (NoFound), requerimos lecturas estables consecutivas para evitar spam
            user_type, row = lookup_row(cam, text)
            disp_vals = ["","",""]
            titles = ["Folio","Nombre","Telefono"]
            auth = False

            if user_type == "PROPIETARIO":
                sec = cdict["owners"]
                auth = is_active_from_row(sec, row)
                disp_vals = _extract_fields(row, sec.get("disp_cols"))
                titles = sec.get("disp_titles", titles)
                pair = sec["wh_active"] if auth else sec["wh_inactive"]
                cat = "ACTIVE" if auth else "INACTIVE"
            elif user_type == "VISITA":
                sec = cdict["visitors"]
                auth = is_active_from_row(sec, row)
                disp_vals = _extract_fields(row, sec.get("disp_cols"))
                titles = sec.get("disp_titles", titles)
                pair = sec["wh_active"] if auth else sec["wh_inactive"]
                cat = "ACTIVE" if auth else "INACTIVE"
            else:
                pair = cdict["wh_notfound"]
                cat = "NOTFOUND"

            # Determinar cantidad de hits requeridos
            if auth:
                needed = 1  # ¡Apertura inmediata e instantánea!
            else:
                if user_type == "NONE":
                    needed = int(cdict.get("notfound_stable_hits_required", 3))
                else:
                    needed = int(cdict.get("stable_hits_required", 2))
                # Si la confianza es extremadamente alta, permitimos 1 hit de confirmación
                if conf >= 0.93 and det_conf >= 0.85:
                    needed = 1

            if key == _stable_state[cam-1]["last"]:
                _stable_state[cam-1]["hits"] += 1
            else:
                _stable_state[cam-1]["last"] = key
                _stable_state[cam-1]["hits"] = 1

            if _stable_state[cam-1]["hits"] < needed:
                time.sleep(0.01)
                continue

            # Suprimir NoFound repetidos por unos segundos después de una lectura válida
            if user_type == "NONE":
                sup = int(cdict.get("suppress_notfound_after_auth_sec", 8))
                if sup > 0 and (time.time() - _last_auth_ts[cam-1]) < sup:
                    time.sleep(0.01)
                    continue

            # Registrar tiempo de última autorización exitosa para supresión
            if auth:
                _last_auth_ts[cam-1] = time.time()

            # Disparar apertura de la barrera física de inmediato
            if auth and cdict.get("gate_enabled", False) and cdict.get("gate_auto_on_auth", False):
                if gate_can_fire(cam):
                    gate_fire(cam)

            # Enviar Webhooks correspondientes
            if user_type != "NONE":
                enqueue_webhooks(cam, cat, pair, user_type, "Placa", text, disp_vals, titles)
            else:
                enqueue_webhooks(cam, "NOTFOUND", pair, "NoFound", "Placa", text, ["","",""], ["Folio","Nombre","Telefono"])

            # Actualizar estado de la interfaz web
            with slock[cam-1]:
                states[cam-1]["plate"] = text
                states[cam-1]["conf"] = float(conf)
                states[cam-1]["ts"] = time.time()
                states[cam-1]["auth"] = bool(auth)
                states[cam-1]["cat"] = cat
                states[cam-1]["display"] = disp_vals
                states[cam-1]["titles"] = titles
                states[cam-1]["user_type"] = user_type

            # Registrar en el log local permanente (inmune a fallas)
            log_event("PLACA", cam, text, float(conf), cat, user_type, auth, disp_vals)

            time.sleep(0.005)

        except Exception as e:
            print(f"[ALPR][cam{cam}] loop exception:", e)
            time.sleep(0.2)



# ========== Seguridad ==========
def _check_token():
    want=(cfg.get("api_token") or "").strip()
    if not want: return True
    got=(request.headers.get("X-API-Key") or request.args.get("api_key") or "").strip()
    return got==want

# ========== UI ==========
HOME = """
 <style>
 body{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;margin:24px;background:#f8fafc;color:#1e293b}
 h1{margin:0 0 12px;font-weight:800;letter-spacing:-0.5px;color:#0f172a;font-size:26px}
 .net{font-size:13px;color:#64748b;margin-bottom:20px;background:#fff;padding:10px 16px;border-radius:10px;box-shadow:0 1px 3px rgba(0,0,0,0.05);display:inline-block;border:1px solid #e2e8f0}
 .grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(340px,1fr));gap:20px}
 .card{border:1px solid #e2e8f0;border-radius:16px;padding:24px;background:#fff;box-shadow:0 4px 6px -1px rgba(0,0,0,0.05), 0 2px 4px -1px rgba(0,0,0,0.03)}
 .card h3{margin:0 0 16px 0;font-size:18px;color:#0f172a;border-bottom:1px solid #f1f5f9;padding-bottom:12px}
 .plate{font-family:"SF Mono",ui-monospace,SFMono-Regular,Menlo,Monaco,Consolas,monospace;font-size:46px;font-weight:800;border:3px solid #0f172a;border-radius:12px;padding:8px 16px;background:#fff;display:inline-block;min-width:240px;text-align:center;box-shadow:inset 0 2px 4px rgba(0,0,0,0.05), 0 4px 6px rgba(0,0,0,0.05);letter-spacing:2px;color:#0f172a;margin-bottom:6px}
 .tag{font-family:"SF Mono",ui-monospace,SFMono-Regular,Menlo,Monaco,Consolas,monospace;font-size:24px;font-weight:700;border:2px dashed #cbd5e1;border-radius:12px;padding:8px 16px;background:#f8fafc;display:inline-block;min-width:240px;text-align:center;color:#64748b;margin-bottom:6px}
 .muted{color:#64748b;font-size:12px} .hit{color:#10b981;font-weight:700} .miss{color:#ef4444;font-weight:700}
 .ok{color:#10b981;font-weight:600} .bad{color:#ef4444;font-weight:600} 
 .btn{padding:8px 14px;border:none;border-radius:8px;background:#f1f5f9;cursor:pointer;font-weight:600;font-size:13px;color:#334155;transition:all 0.2s;text-decoration:none;display:inline-flex;align-items:center;justify-content:center}
 .btn:hover{background:#e2e8f0;transform:translateY(-1px)}
 .dot{display:inline-block;width:10px;height:10px;border-radius:50%;margin:0 6px;vertical-align:middle;box-shadow:0 0 0 2px #fff}
 .on{background:#10b981;box-shadow:0 0 0 2px #fff, 0 0 8px #10b981}.off{background:#cbd5e1}
 .row{display:flex;gap:16px;flex-wrap:wrap;align-items:center}
 .k{font-weight:700;text-transform:uppercase;font-size:11px;letter-spacing:0.5px;color:#94a3b8;margin-bottom:6px}
 </style>
<h1>{{title}}</h1>
<div class="net">
  Wi-Fi: <b id="net_ssid">—</b> • Señal: <b id="net_sig">—</b>% • IP: <b id="net_ip">—</b>
  &nbsp; | &nbsp; Temp: <b id="sys_temp">—</b>°C • CPU: <b id="sys_cpu">—</b>%
  &nbsp; | &nbsp; Gate Serial: <b id="gs_conn">—</b> <span class="muted" id="gs_dev"></span>
</div>

<div class="card">
  <div class="row" style="align-items:center">
    <div><b>Estado:</b></div>
    {% for cam in [1,2] %}
      <div>Cam {{cam}} Conexión: <b id="lan{{cam}}">—</b> • Motion <span class="dot" id="m{{cam}}"></span>
      <span class="muted">(Δpix: <span id="mp{{cam}}">—</span>%)</span>
      • Cola: <b id="q{{cam}}">—</b></div>
    {% endfor %}
    <div style="flex:1"></div>
    <a class="btn" href="/wifi" style="margin-right:8px;background:#17a2b8;color:#fff;text-decoration:none">📡 WiFi</a>
    <a class="btn" href="/logs" style="margin-right:8px;background:#28a745;color:#fff;text-decoration:none">📝 Logs</a>
    <a class="btn" href="/settings">⚙️ Settings</a>
  </div>
</div>

<div class="grid">
  {% for cam in [1,2] %}
  <div class="card">
    <h3 style="margin:6px 0">Cam {{cam}}</h3>
    <div class="row">
      <div>
        <div class="k">Placa</div>
        <div class="plate" id="p{{cam}}">Sin Placa</div>
        <div class="muted">Conf: <span id="cf{{cam}}">—</span>% • Hora: <span id="ts{{cam}}">—</span></div>
        <div>Usuario: <b id="usr{{cam}}">—</b> • WL: <span id="wl{{cam}}">—</span></div>
        <div class="muted" id="f{{cam}}"></div>
      </div>
      <div>
        <div class="k">Tag</div>
        <div class="tag" id="t{{cam}}">—</div>
        <div>WL: <span id="twl{{cam}}">—</span></div>
        <div class="muted" id="tf{{cam}}"></div>
      </div>
    </div>
    <div style="margin-top:8px" class="row">
      <a class="btn" href="/snapshot.jpg?cam={{cam}}&w=640" target="_blank">📸 Snapshot</a>
      <a class="btn" href="/snapshot_pre.jpg?cam={{cam}}&w=640" target="_blank">🧪 Preproc</a>
      <a class="btn" href="/roi?cam={{cam}}" target="_blank">✂ ROI</a>
      <button class="btn" onclick="openGate({{cam}})">🟩 Abrir pluma</button>
      <span class="muted" id="msg{{cam}}"></span>
    </div>
  </div>
  {% endfor %}
</div>

<script>
async function poll(){
  try{
    const nn=await (await fetch('/api/net')).json();
    document.getElementById('net_ssid').textContent=nn.ssid||'—';
    document.getElementById('net_sig').textContent=nn.signal||'—';
    document.getElementById('net_ip').textContent=nn.ip||'—';
  }catch(e){}
  try{
    const ss=await (await fetch('/api/sys')).json();
    document.getElementById('sys_temp').textContent = (ss.temp_c==null?'—':(+ss.temp_c).toFixed(1));
    document.getElementById('sys_cpu').textContent = (ss.cpu_pct==null?'—':(+ss.cpu_pct).toFixed(1));
  }catch(e){}
  try{
    const gs=await (await fetch('/api/gate_serial_status')).json();
    document.getElementById('gs_conn').textContent = (gs.connected?'Conectado':'No');
    document.getElementById('gs_conn').className = gs.connected?'ok':'bad';
    document.getElementById('gs_dev').textContent = gs.device?('('+gs.device+')'):'';
  }catch(e){}

  try{
    const j=await (await fetch('/api/lan')).json();
    for(let cam=1; cam<=2; cam++){
      const t=j['cam'+cam]||{};
      const el=document.getElementById('lan'+cam);
      el.textContent=t.ok?('Conectada ('+(t.ip||'—')+')'):'Sin conexión';
      el.className=t.ok?'ok':'bad';
    }
  }catch(e){}
  try{
    const mj=await (await fetch('/api/motion')).json();
    for(let cam=1; cam<=2; cam++){
      const d=document.getElementById('m'+cam);
      d.className='dot '+(mj['cam'+cam]?.active?'on':'off');
      document.getElementById('mp'+cam).textContent = (mj['cam'+cam]?.ratio==null?'—':mj['cam'+cam].ratio.toFixed(2));
      const q = mj['cam'+cam]?.queue||{};
      document.getElementById('q'+cam).textContent = (q.pending==null?'—':(q.pending+' pend / '+(q.dropped||0)+' drop'));
    }
  }catch(e){}
  for(let cam=1; cam<=2; cam++){
    try{
      const s=await (await fetch('/api/status?cam='+cam)).json();
      if(!s.plate){
        document.getElementById('p'+cam).textContent='Sin Placa';
        document.getElementById('cf'+cam).textContent='—';
        document.getElementById('ts'+cam).textContent='—';
        document.getElementById('usr'+cam).textContent='—';
        const wl=document.getElementById('wl'+cam); wl.textContent='—'; wl.className='';
        document.getElementById('f'+cam).textContent='';
      }else{
        document.getElementById('p'+cam).textContent=s.plate;
        document.getElementById('cf'+cam).textContent=(Number(s.conf||0)*100).toFixed(1);
        document.getElementById('ts'+cam).textContent=s.ts ? new Date(s.ts*1000).toLocaleTimeString() : '—';
        document.getElementById('usr'+cam).textContent=s.user_type||'—';
        const wl=document.getElementById('wl'+cam);
        wl.textContent=(s.category==='ACTIVE')?'EN WHITELIST (ACTIVO)':(s.category==='INACTIVE'?'EN WHITELIST (INACTIVO)':'NOFOUND');
        wl.className=(s.category==='ACTIVE')?'hit':((s.category==='INACTIVE')?'miss':'miss');
        document.getElementById('f'+cam).textContent=(s.fields||[]).filter(Boolean).join(' • ');
      }

      if(!s.tag){
        document.getElementById('t'+cam).textContent='—';
        const twl=document.getElementById('twl'+cam); twl.textContent='—'; twl.className='';
        document.getElementById('tf'+cam).textContent='';
      }else{
        document.getElementById('t'+cam).textContent=s.tag;
        const twl=document.getElementById('twl'+cam);
        twl.textContent=(s.tag_cat==='ACTIVE')?'TAG ACTIVO':(s.tag_cat==='INACTIVE'?'TAG INACTIVO':'TAG NOFOUND');
        twl.className=(s.tag_cat==='ACTIVE')?'hit':'miss';
        document.getElementById('tf'+cam).textContent=(s.tag_fields||[]).filter(Boolean).join(' • ');
      }
    }catch(e){}
  }
}

async function openGate(cam){
  const m=document.getElementById('msg'+cam); m.textContent="Enviando…";
  try{
    const r=await fetch('/api/gate_open?cam='+cam,{method:'POST'}); const j=await r.json();
    m.textContent=j.ok?'Pluma abierta':'Error: '+(j.error||'');
  }catch(e){m.textContent='Error: '+e;} finally{setTimeout(()=>m.textContent='',1500);}
}

setInterval(poll,500);
poll();
</script>
"""

ROI_HTML = """<!doctype html><meta charset="utf-8"><title>ROI Cam {{cam}}</title>
<style>
 body{font-family:system-ui;margin:16px;background:#fafafa}
 .row{display:flex;gap:16px;align-items:flex-start;flex-wrap:wrap}
 .card{border:1px solid #ddd;border-radius:12px;padding:12px;background:#fff}
 .btn{padding:8px 12px;border:1px solid #888;border-radius:10px;background:#f5f5f5;cursor:pointer}
 .muted{color:#666;font-size:12px}
 canvas{max-width:100%; height:auto; border:1px solid #aaa; border-radius:8px}
 img.preview{max-width:100%; height:auto; border:1px solid #aaa; border-radius:8px}
 .col{min-width:320px; flex:1}
 .title{font-weight:700;margin-bottom:8px}
</style>
<h2>Definir ROI — Cam {{cam}}</h2>

<div class="row">
  <div class="card col">
    <div class="title">1) Dibuja ROI sobre imagen normal</div>
    <img id="raw" src="" crossorigin="anonymous" style="display:none"/>
    <canvas id="cnv"></canvas>

    <div style="margin-top:8px">
      <label><input type="checkbox" id="enabled"> Habilitar ROI</label>
      <button class="btn" id="saveBtn">💾 Guardar ROI</button>
      <button class="btn" id="clearBtn">🧹 Limpiar</button>
      <a class="btn" href="/">⬅ Volver</a>
      <span class="muted" id="msg"></span>
    </div>

    <div class="muted" style="margin-top:6px">
      Arrastra para dibujar el rectángulo. Se guarda normalizado.
    </div>
  </div>

  <div class="card col">
    <div class="title">2) Vista ALPR en vivo (ROI + preprocesado)</div>
    <img id="proc" class="preview" src="" alt="Vista ALPR"/>
    <div class="muted" style="margin-top:6px">
      Esta vista intenta mostrar exactamente lo que entra a ALPR (recorte ROI + preprocesado activado en Settings).
    </div>
    <div class="muted" style="margin-top:6px"><b>ROI actual</b><pre id="cur"></pre></div>
  </div>
</div>

<script>
const cam={{cam}};
const imgEl=document.getElementById('raw');
const cnv=document.getElementById('cnv');
const ctx=cnv.getContext('2d');
const proc=document.getElementById('proc');

// Dimensiones FIJAS del canvas (se establecen al cargar la primera imagen y NO cambian).
// Esto evita que el ROI "se mueva" cuando refrescamos el snapshot.
let canvasW=0, canvasH=0;

let roi={x:0,y:0,w:1,h:1,enabled:false};
let dragging=false, sx=0, sy=0, ex=0, ey=0;

function draw(){
  if(!canvasW || !canvasH) return;
  ctx.clearRect(0,0,canvasW,canvasH);
  if(imgEl.complete && imgEl.naturalWidth>0){
    ctx.drawImage(imgEl, 0, 0, canvasW, canvasH);
  }
  // ROI guardado (verde)
  if(roi.w>0.01 && roi.h>0.01){
    ctx.lineWidth=2; ctx.strokeStyle='rgba(0,200,0,0.9)';
    ctx.setLineDash([6,4]);
    ctx.strokeRect(roi.x*canvasW, roi.y*canvasH, roi.w*canvasW, roi.h*canvasH);
    ctx.setLineDash([]);
  }
  // Rectángulo arrastrando (naranja)
  if(dragging){
    const x=Math.min(sx,ex), y=Math.min(sy,ey);
    const w=Math.abs(ex-sx), h=Math.abs(ey-sy);
    ctx.lineWidth=2; ctx.strokeStyle='rgba(255,140,0,0.9)';
    ctx.strokeRect(x,y,w,h);
  }
}

// Convierte coordenadas CSS (del evento mouse/touch) a coordenadas internas del canvas.
// Usa las dimensiones CSS actuales del canvas (que cambian con el viewport) y las
// escala a las dimensiones internas fijas (canvasW x canvasH).
function _toCanvasXY(e){
  const r = cnv.getBoundingClientRect();
  const cx = (e.clientX - r.left);
  const cy = (e.clientY - r.top);
  const scaleX = canvasW / Math.max(1, r.width);
  const scaleY = canvasH / Math.max(1, r.height);
  return {x: cx*scaleX, y: cy*scaleY};
}

function _startDrag(e){
  e.preventDefault();
  const p=_toCanvasXY(e);
  sx=p.x; sy=p.y; ex=sx; ey=sy; dragging=true; draw();
}
function _moveDrag(e){
  if(!dragging) return;
  e.preventDefault();
  const p=_toCanvasXY(e);
  ex=p.x; ey=p.y; draw();
}
function _endDrag(e){
  if(!dragging) return;
  e.preventDefault();
  dragging=false;
  const x=Math.max(0, Math.min(sx,ex)) / canvasW;
  const y=Math.max(0, Math.min(sy,ey)) / canvasH;
  const w=Math.abs(ex-sx) / canvasW;
  const h=Math.abs(ey-sy) / canvasH;
  if(w>0.01 && h>0.01){ roi.x=x; roi.y=y; roi.w=w; roi.h=h; }
  draw();
}

// Mouse
cnv.addEventListener('mousedown', _startDrag);
cnv.addEventListener('mousemove', _moveDrag);
window.addEventListener('mouseup', _endDrag);

// Touch
cnv.addEventListener('touchstart', (ev)=>{ if(ev.touches && ev.touches[0]) _startDrag(ev.touches[0]); }, {passive:false});
cnv.addEventListener('touchmove',  (ev)=>{ if(ev.touches && ev.touches[0]) _moveDrag(ev.touches[0]);  }, {passive:false});
window.addEventListener('touchend', (ev)=>{ _endDrag(ev.changedTouches && ev.changedTouches[0] ? ev.changedTouches[0] : ev); }, {passive:false});

async function loadCur(){
  const r=await fetch('/api/roi_get?cam='+cam);
  const j=await r.json();
  roi=j.roi||roi;
  document.getElementById('enabled').checked=!!roi.enabled;
  document.getElementById('cur').textContent=JSON.stringify(roi, null, 2);
  draw();
}

document.getElementById('saveBtn').onclick=async ()=>{
  const enabled=document.getElementById('enabled').checked;
  const body={x:roi.x,y:roi.y,w:roi.w,h:roi.h,enabled};
  const r=await fetch('/api/roi_save?cam='+cam,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});
  const j=await r.json();
  document.getElementById('msg').textContent=(j.error||j.message||'');
  await loadCur();
  refreshProcessed();
};

document.getElementById('clearBtn').onclick=async ()=>{
  const r=await fetch('/api/roi_clear?cam='+cam,{method:'POST'});
  const j=await r.json();
  document.getElementById('msg').textContent=(j.error||j.message||'');
  await loadCur();
  refreshProcessed();
};

async function refreshSnapshot(){
  const tmp = new Image();
  tmp.crossOrigin='anonymous';
  tmp.onload = ()=>{
    // Primera vez: fijar dimensiones del canvas a las de la imagen real
    if(!canvasW || !canvasH){
      canvasW = tmp.naturalWidth;
      canvasH = tmp.naturalHeight;
      cnv.width  = canvasW;
      cnv.height = canvasH;
    }
    // Actualizar el src del img original para que draw() lo use
    imgEl.src = tmp.src;
    draw();
  };
  tmp.onerror = ()=>{ setTimeout(refreshSnapshot, 800); };
  tmp.src = '/snapshot.jpg?cam='+cam+'&w=1280&q=90&ts='+(Date.now());
}

async function refreshProcessed(){
  proc.src='/snapshot_alpr.jpg?cam='+cam+'&w=1280&q=90&ts='+(Date.now());
}

window.onload=async ()=>{
  await loadCur();
  await refreshSnapshot();
  refreshProcessed();
  setInterval(refreshSnapshot, 4000);
  setInterval(refreshProcessed, 1200);
}
</script>
"""

def _fmt_cols(v):
    if isinstance(v, list):
        out=[]
        for x in v[:3]:
            out.append("" if x is None else str(x))
        while len(out)<3: out.append("")
        return out
    return ["2","3","4"]

def _pair_get(p, k, fb=""):
    return (p.get(k, fb) if isinstance(p, dict) else fb)

SETTINGS_INDEX = """
<style>
 body{font-family:system-ui;margin:18px;background:#fafafa}
 .card{border:1px solid #ddd;border-radius:12px;padding:14px;max-width:980px;background:#fff}
 .btn{padding:8px 12px;border:1px solid #888;border-radius:10px;background:#f5f5f5;cursor:pointer}
 input[type="text"],input[type="number"]{padding:6px 8px;border-radius:8px;border:1px solid #bbb;min-width:260px}
 label{display:block;margin:6px 0}
 .muted{color:#666;font-size:12px}
</style>
<h2>Settings</h2>
<div class="card">
  <p>
    <a class="btn" href="/settings/1">⚙️ Cam 1</a>
    <a class="btn" href="/roi?cam=1" target="_blank">✂ ROI 1</a>
  </p>
  <p>
    <a class="btn" href="/settings/2">⚙️ Cam 2</a>
    <a class="btn" href="/roi?cam=2" target="_blank">✂ ROI 2</a>
  </p>
  <hr>
  <form method="post">
    <h3>Seguridad</h3>
    <label>API Token (X-API-Key / ?api_key=):
      <input type="text" name="api_token" value="{{api_token}}" placeholder="opcional">
    </label>
    <h3>Monitor (opcional)</h3>
    <label><input type="checkbox" name="monitor_enabled" {{'checked' if monitor_enabled else ''}}> Enviar heartbeat</label>
    <label>Monitor URL:
      <input type="text" name="monitor_url" value="{{monitor_url}}" placeholder="https://...">
    </label>
    <label>Periodo (min):
      <input type="number" step="1" name="monitor_period_min" value="{{monitor_period_min}}">
    </label>
    
    <p>
      <button class="btn" name="action" value="heartbeat_test">📡 Probar heartbeat ahora</button>
      <span class="muted">{{hb_msg}}</span>
    </p>
    <p class="muted">
      Último OK: <b>{{hb_last_ok}}</b> • Último intento: <b>{{hb_last_try}}</b> • Code: <b>{{hb_last_code}}</b> • Error: <b>{{hb_last_err}}</b>
    </p>
<p class="muted">El heartbeat incluye temp/cpu/colas y último estado por cámara.</p>
    <p style="margin-top:10px">
      <button class="btn">Guardar</button>
      <a class="btn" href="/">Volver</a>
    </p>
  </form>
</div>
"""

def _pair_block(prefix, pair):
    # prefix: string for input names
    # pair: dict
    u1=_pair_get(pair,"url1",""); u2=_pair_get(pair,"url2","")
    s1=bool(_pair_get(pair,"send_snapshot1",False)); s2=bool(_pair_get(pair,"send_snapshot2",False))
    m1=_pair_get(pair,"snapshot_mode1","multipart") or "multipart"
    m2=_pair_get(pair,"snapshot_mode2","multipart") or "multipart"
    return f"""
<div class="grid3">
  <label>URL #1<br><input type="text" name="{prefix}_url1" value="{u1}" placeholder="https://..."></label>
  <label>Snapshot #1<br>
    <select name="{prefix}_send_snapshot1">
      <option value="0" {"selected" if not s1 else ""}>OFF</option>
      <option value="1" {"selected" if s1 else ""}>ON</option>
    </select>
  </label>
  <label>Modo #1<br>
    <select name="{prefix}_snapshot_mode1">
      <option value="multipart" {"selected" if m1=="multipart" else ""}>multipart</option>
      <option value="json" {"selected" if m1=="json" else ""}>json</option>
    </select>
  </label>
</div>
<div class="grid3">
  <label>URL #2<br><input type="text" name="{prefix}_url2" value="{u2}" placeholder="https://..."></label>
  <label>Snapshot #2<br>
    <select name="{prefix}_send_snapshot2">
      <option value="0" {"selected" if not s2 else ""}>OFF</option>
      <option value="1" {"selected" if s2 else ""}>ON</option>
    </select>
  </label>
  <label>Modo #2<br>
    <select name="{prefix}_snapshot_mode2">
      <option value="multipart" {"selected" if m2=="multipart" else ""}>multipart</option>
      <option value="json" {"selected" if m2=="json" else ""}>json</option>
    </select>
  </label>
</div>
"""

SETTINGS_CAM = """
<style>
 body{font-family:system-ui;margin:18px;background:#fafafa}
 .card{border:1px solid #ddd;border-radius:12px;padding:14px;max-width:1200px;background:#fff}
 label{display:block;margin:6px 0}
 input[type="text"],input[type="number"]{padding:6px 8px;border-radius:8px;border:1px solid #bbb;min-width:240px}
 select{padding:6px 8px;border-radius:8px;border:1px solid #bbb;min-width:160px}
 .btn{padding:8px 12px;border:1px solid #888;border-radius:10px;background:#f5f5f5;cursor:pointer}
 .muted{color:#666;font-size:12px}
 .grid{display:grid;grid-template-columns:repeat(2,minmax(280px,1fr));gap:10px 24px}
 .grid3{display:grid;grid-template-columns:repeat(3,minmax(220px,1fr));gap:10px 16px}
 .grid4{display:grid;grid-template-columns:repeat(4,minmax(180px,1fr));gap:10px 16px}
 .subsec{border:1px dashed #aaa;padding:10px;border-radius:10px;margin:8px 0;background:#fcfcfc}
 .hl{background:#fffbec}
 .a{color:#0645ad;text-decoration:none}
 .a:hover{text-decoration:underline}
 hr{border:none;border-top:1px solid #eee;margin:12px 0}
</style>

<h2>Settings — Cam {{cam}}</h2>
<form method="post" class="card">
  <div class="subsec hl">
    <b>Dedup / Gap (aplica a TODO: Activo/Inactivo/NoFound + Tags)</b>
    <div class="grid">
      <label>Permitir repetir misma placa/tag<br>
        <select name="wh_repeat_same_plate">
          <option value="0" {{'selected' if not c.wh_repeat_same_plate else ''}}>NO (recomendado)</option>
          <option value="1" {{'selected' if c.wh_repeat_same_plate else ''}}>SI</option>
        </select>
      </label>
      <label>Min gap (seg) si se permite repetir<br>
        <input type="number" name="wh_min_gap_sec" value="{{c.wh_min_gap_sec}}">
      </label>
    </div>
    <div class="muted">Si NO permites repetir, la misma placa/tag solo dispara cuando cambia.</div>
  </div>

  <h3>Cámara</h3>
  <div class="grid">
    <label>Modo<br>
      <select name="camera_mode">
        <option value="mac" {{ 'selected' if c.camera_mode=='mac' else '' }}>Por MAC ({CAM_IP})</option>
        <option value="manual" {{ 'selected' if c.camera_mode=='manual' else '' }}>URL manual</option>
      </select>
    </label>
    <label>camera_mac<br><input type="text" name="camera_mac" value="{{c.camera_mac}}" placeholder="AA:BB:CC:DD:EE:FF"></label>
    <label style="grid-column:1/-1">RTSP URL<br><input type="text" name="camera_url" value="{{c.camera_url}}" style="min-width:95%" placeholder="rtsp://...@{CAM_IP}:554/..."></label>
    <label><input type="checkbox" name="roi_enabled" {{ 'checked' if c.roi.enabled else '' }}> Habilitar ROI</label>
    <div class="muted">Define ROI en <a class="a" href="/roi?cam={{cam}}" target="_blank">/roi?cam={{cam}}</a></div>
  </div>

  <div class="subsec hl" style="margin-top: 15px;">
    <b>⚙️ Rendimiento y Optimización de IA (Autopreparado)</b>
    <div class="muted" style="margin-top: 5px; line-height: 1.4;">
      El portal ha sido configurado en su <b>configuración base óptima</b> para Raspberry Pi 5. Los parámetros de red neuronal, tamaño de red (800px), confianza mínima (85%), filtrado bilateral lento (desactivado) y tasa de frames han sido bloqueados en el sistema para garantizar el funcionamiento más veloz y estable del procesador.
    </div>
  </div>

  <h3>Motion gating (Detección de Movimiento)</h3>
  <div class="grid">
    <label><input type="checkbox" name="motion_enabled" {{'checked' if c.motion.enabled else ''}}> Habilitar Detección de Movimiento en ROI</label>
    <label>Umbral cambio pix (%)<br>
      <input type="number" step="0.1" name="motion_pixel_change_pct" value="{{c.motion.pixel_change_pct}}">
    </label>
  </div>
  <div class="muted">Si se habilita, la Inteligencia Artificial solo procesará imágenes cuando se detecte movimiento dentro de la zona de interés (ROI). El umbral define qué porcentaje de píxeles debe cambiar para activarse (típico: 2.0% a 8.0%).</div>

  <h3>Gate / ESP32</h3>
  <div class="grid">
    <label><input type="checkbox" name="gate_enabled" {{'checked' if c.gate_enabled else ''}}> Habilitar Gate</label>
    <label>Modo Gate<br>
      <select name="gate_mode">
        <option value="serial" {{'selected' if c.gate_mode=='serial' else ''}}>SERIAL/USB (recomendado)</option>
        <option value="http" {{'selected' if c.gate_mode=='http' else ''}}>HTTP/IP</option>
      </select>
    </label>
    <label><input type="checkbox" name="gate_auto_on_auth" {{'checked' if c.gate_auto_on_auth else ''}}> Abrir automáticamente si ACTIVO</label>
    <label>Anti-spam (s)<br><input type="number" name="gate_antispam_sec" value="{{c.gate_antispam_sec}}"></label>
    <label>Pulso (ms)<br><input type="number" name="gate_pulse_ms" value="{{c.gate_pulse_ms}}"></label>
  </div>

  <div class="subsec">
    <b>HTTP/IP</b>
    <div class="grid4">
      <label>ESP32 URL<br><input type="text" name="gate_url" value="{{c.gate_url}}" placeholder="http://ip-del-esp32"></label>
      <label>Token<br><input type="text" name="gate_token" value="{{c.gate_token}}"></label>
      <label>GPIO pin<br><input type="number" name="gate_pin" value="{{c.gate_pin}}"></label>
      <label>Active Low<br>
        <select name="gate_active_low">
          <option value="0" {{'selected' if not c.gate_active_low else ''}}>NO</option>
          <option value="1" {{'selected' if c.gate_active_low else ''}}>SI</option>
        </select>
      </label>
    </div>
  </div>

  <div class="subsec">
    <b>SERIAL/USB</b>
    <div class="grid3">
      <label>Device (vacío=autodetect)<br><input type="text" name="gate_serial_device" value="{{c.gate_serial_device}}" placeholder="/dev/serial/by-id/..."></label>
      <label>Baud<br><input type="number" name="gate_serial_baud" value="{{c.gate_serial_baud}}"></label>
      <label>Gate # (JSON gate=)<br><input type="number" name="gate_serial_gate" value="{{c.gate_serial_gate}}"></label>
    </div>
    <div class="muted">ESP32 debe aceptar JSONL: {"cmd":"pulse","gate":N,"ms":M}</div>
  </div>

  <hr>
  <h3>WHITELISTS (Placas)</h3>

  <div class="subsec">
    <b>Propietarios</b>
    <div class="grid">
      <label>Sheets (ID o URL)<br><input type="text" name="owners_sheets_input" value="{{owners.sheets_input}}"></label>
      <label>Auto refresh (min, 0=off)<br><input type="number" name="owners_auto_refresh_min" value="{{owners.auto_refresh_min}}"></label>
      <label>Buscar placas desde col<br><input type="text" name="owners_search_start_col" value="{{owners.search_start_col}}"></label>
      <label>hasta col<br><input type="text" name="owners_search_end_col" value="{{owners.search_end_col}}"></label>
      <label>Status col<br><input type="text" name="owners_status_col" value="{{owners.status_col}}"></label>
      <label>Disp col 1<br><input type="text" name="owners_disp_col_1" value="{{owners.disp_cols[0]}}"></label>
      <label>Disp col 2<br><input type="text" name="owners_disp_col_2" value="{{owners.disp_cols[1]}}"></label>
      <label>Disp col 3<br><input type="text" name="owners_disp_col_3" value="{{owners.disp_cols[2]}}"></label>
      <label>Título 1<br><input type="text" name="owners_disp_title_1" value="{{owners.disp_titles[0]}}"></label>
      <label>Título 2<br><input type="text" name="owners_disp_title_2" value="{{owners.disp_titles[1]}}"></label>
      <label>Título 3<br><input type="text" name="owners_disp_title_3" value="{{owners.disp_titles[2]}}"></label>
    </div>

    <div class="subsec">
      <b>Webhooks Owners — ACTIVO</b>
      {{owners_wh_active|safe}}
    </div>
    <div class="subsec">
      <b>Webhooks Owners — INACTIVO</b>
      {{owners_wh_inactive|safe}}
    </div>

    <p>
      <button class="btn" name="action" value="refresh_owners">🔄 Refresh Owners WL</button>
      <span class="muted">{{owners_refresh_msg}}</span>
    </p>
  </div>

  <div class="subsec">
    <b>Visitas</b>
    <div class="grid">
      <label>Sheets (ID o URL)<br><input type="text" name="visitors_sheets_input" value="{{visitors.sheets_input}}"></label>
      <label>Auto refresh (min, 0=off)<br><input type="number" name="visitors_auto_refresh_min" value="{{visitors.auto_refresh_min}}"></label>
      <label>Buscar placas desde col<br><input type="text" name="visitors_search_start_col" value="{{visitors.search_start_col}}"></label>
      <label>hasta col<br><input type="text" name="visitors_search_end_col" value="{{visitors.search_end_col}}"></label>
      <label>Status col<br><input type="text" name="visitors_status_col" value="{{visitors.status_col}}"></label>
      <label>Disp col 1<br><input type="text" name="visitors_disp_col_1" value="{{visitors.disp_cols[0]}}"></label>
      <label>Disp col 2<br><input type="text" name="visitors_disp_col_2" value="{{visitors.disp_cols[1]}}"></label>
      <label>Disp col 3<br><input type="text" name="visitors_disp_col_3" value="{{visitors.disp_cols[2]}}"></label>
      <label>Título 1<br><input type="text" name="visitors_disp_title_1" value="{{visitors.disp_titles[0]}}"></label>
      <label>Título 2<br><input type="text" name="visitors_disp_title_2" value="{{visitors.disp_titles[1]}}"></label>
      <label>Título 3<br><input type="text" name="visitors_disp_title_3" value="{{visitors.disp_titles[2]}}"></label>
    </div>

    <div class="subsec">
      <b>Webhooks Visitas — ACTIVO</b>
      {{visitors_wh_active|safe}}
    </div>
    <div class="subsec">
      <b>Webhooks Visitas — INACTIVO</b>
      {{visitors_wh_inactive|safe}}
    </div>

    <p>
      <button class="btn" name="action" value="refresh_visitors">🔄 Refresh Visits WL</button>
      <span class="muted">{{visitors_refresh_msg}}</span>
    </p>
  </div>

  <div class="subsec">
    <b>NoFound (Placas) — 2 webhooks</b>
    {{plates_notfound|safe}}
  </div>

  <hr>
  <h3>TAGS</h3>

  <div class="subsec">
    <b>Formato lookup</b><br>
    <select name="tags_lookup_format">
      <option value="physical" {{'selected' if tags_lookup_format=='physical' else ''}}>physical (recomendado)</option>
      <option value="internal_hex" {{'selected' if tags_lookup_format=='internal_hex' else ''}}>internal_hex</option>
    </select>
  </div>

  <div class="subsec">
    <b>Tags Owners (solo propietarios)</b>
    <div class="grid">
      <label>Sheets (ID o URL)<br><input type="text" name="tags_owners_sheets_input" value="{{tags_owners.sheets_input}}"></label>
      <label>Auto refresh (min, 0=off)<br><input type="number" name="tags_owners_auto_refresh_min" value="{{tags_owners.auto_refresh_min}}"></label>
      <label>Buscar tags desde col<br><input type="text" name="tags_owners_search_start_col" value="{{tags_owners.search_start_col}}"></label>
      <label>hasta col<br><input type="text" name="tags_owners_search_end_col" value="{{tags_owners.search_end_col}}"></label>
      <label>Status col<br><input type="text" name="tags_owners_status_col" value="{{tags_owners.status_col}}"></label>
      <label>Disp col 1<br><input type="text" name="tags_owners_disp_col_1" value="{{tags_owners.disp_cols[0]}}"></label>
      <label>Disp col 2<br><input type="text" name="tags_owners_disp_col_2" value="{{tags_owners.disp_cols[1]}}"></label>
      <label>Disp col 3<br><input type="text" name="tags_owners_disp_col_3" value="{{tags_owners.disp_cols[2]}}"></label>
      <label>Título 1<br><input type="text" name="tags_owners_disp_title_1" value="{{tags_owners.disp_titles[0]}}"></label>
      <label>Título 2<br><input type="text" name="tags_owners_disp_title_2" value="{{tags_owners.disp_titles[1]}}"></label>
      <label>Título 3<br><input type="text" name="tags_owners_disp_title_3" value="{{tags_owners.disp_titles[2]}}"></label>
    </div>

    <div class="subsec">
      <b>Webhooks Tags Owners — ACTIVO</b>
      {{tags_owners_wh_active|safe}}
    </div>
    <div class="subsec">
      <b>Webhooks Tags Owners — INACTIVO</b>
      {{tags_owners_wh_inactive|safe}}
    </div>

    <p>
      <button class="btn" name="action" value="refresh_tags">🔄 Refresh Tags WL</button>
      <span class="muted">{{tags_refresh_msg}}</span>
    </p>
  </div>

  <div class="subsec">
    <b>NoFound (Tags) — 2 webhooks</b>
    {{tags_notfound|safe}}
  </div>

  <p style="margin-top:12px">
    <button class="btn" type="submit" name="action" value="save">Guardar</button>
    <button class="btn" type="submit" name="action" value="copy_to_other">Copiar esta configuración a Cam {{2 if cam==1 else 1}}</button>
    <a class="btn" href="/">Volver</a>
  </p>
</form>
"""

# ---------- Web app ----------
app=Flask(__name__)

@app.route("/")
def home():
    return render_template_string(HOME, title=APP_TITLE)

@app.route("/settings", methods=["GET","POST"])
def settings_index():
    global cfg
    hb_msg=""
    if request.method=="POST":
        action=(request.form.get("action") or "save").strip()

        # Guardar settings
        cfg["api_token"]=(request.form.get("api_token") or "").strip()
        cfg["monitor_enabled"]=bool(request.form.get("monitor_enabled"))
        cfg["monitor_url"]=(request.form.get("monitor_url") or "").strip()
        cfg["monitor_period_min"]=_clampi(request.form.get("monitor_period_min", cfg.get("monitor_period_min",0)),0,1440,cfg.get("monitor_period_min",0))
        save_cfg(cfg)

        # Acción: probar heartbeat (no bloquea)
        if action=="heartbeat_test":
            # encolado inmediato, el envío lo hace el thread dedicado
            try:
                heartbeat_mgr.enqueue("manual_test")
                hb_msg="Encolado (manual_test). Revisa el receptor / monitor."
            except Exception as e:
                hb_msg=f"Error encolando: {e}"
        else:
            hb_msg="Guardado."

    def _fmt_ts(ts):
        try:
            ts=float(ts or 0.0)
            if ts<=0: return "—"
            return datetime.datetime.fromtimestamp(ts, tz=TZ).strftime("%Y-%m-%d %H:%M:%S")
        except Exception:
            return "—"

    return render_template_string(
        SETTINGS_INDEX,
        api_token=cfg.get("api_token",""),
        monitor_enabled=cfg.get("monitor_enabled",False),
        monitor_url=cfg.get("monitor_url",""),
        monitor_period_min=cfg.get("monitor_period_min",0),
        hb_msg=hb_msg,
        hb_last_ok=_fmt_ts(hb_status.get("last_ok_ts",0.0)),
        hb_last_try=_fmt_ts(hb_status.get("last_try_ts",0.0)),
        hb_last_code=(hb_status.get("last_code", None) if hb_status.get("last_code",None) is not None else "—"),
        hb_last_err=(hb_status.get("last_err","") or "—"),
    )


def _copy_cam_settings(src_cam:int, dst_cam:int):
    src_cfg = deepcopy(cfg["cameras"][src_cam-1])
    dst_cfg = deepcopy(cfg["cameras"][dst_cam-1])

    # conservar valores que suelen ser propios de cada cámara
    preserve_keys = {
        "camera_mac",
        "camera_url",
        "gate_url",
        "gate_pin",
        "gate_serial_gate",
        "gate_serial_device",
    }

    merged = deepcopy(src_cfg)
    for k in preserve_keys:
        if k in dst_cfg:
            merged[k] = deepcopy(dst_cfg[k])

    cfg["cameras"][dst_cam-1] = merged
    save_cfg(cfg)
    return f"Configuración general de Cam {src_cam} copiada a Cam {dst_cam}"

def _pull_pair_from_form(prefix:str):
    return {
        "url1": (request.form.get(prefix+"_url1") or "").strip(),
        "send_snapshot1": _parse_bool_form(request.form.get(prefix+"_send_snapshot1","0")),
        "snapshot_mode1": (request.form.get(prefix+"_snapshot_mode1") or "multipart").strip(),
        "url2": (request.form.get(prefix+"_url2") or "").strip(),
        "send_snapshot2": _parse_bool_form(request.form.get(prefix+"_send_snapshot2","0")),
        "snapshot_mode2": (request.form.get(prefix+"_snapshot_mode2") or "multipart").strip(),
    }

def _section_from_form(prefix:str, sec:dict):
    sec["sheets_input"] = (request.form.get(prefix+"_sheets_input") or "").strip()
    sec["auto_refresh_min"] = _clampi(request.form.get(prefix+"_auto_refresh_min", sec.get("auto_refresh_min",0)), 0, 1440, sec.get("auto_refresh_min",0))
    sec["search_start_col"] = col_to_idx(request.form.get(prefix+"_search_start_col", sec.get("search_start_col",14)), sec.get("search_start_col",14))
    sec["search_end_col"]   = col_to_idx(request.form.get(prefix+"_search_end_col", sec.get("search_end_col",18)), sec.get("search_end_col",18))
    if sec["search_end_col"] < sec["search_start_col"]:
        sec["search_end_col"] = sec["search_start_col"]
    sec["status_col"] = col_to_idx(request.form.get(prefix+"_status_col", sec.get("status_col",3)), sec.get("status_col",3))
    c1=request.form.get(prefix+"_disp_col_1", sec.get("disp_cols",[2,3,4])[0])
    c2=request.form.get(prefix+"_disp_col_2", sec.get("disp_cols",[2,3,4])[1])
    c3=request.form.get(prefix+"_disp_col_3", sec.get("disp_cols",[2,3,4])[2])
    sec["disp_cols"] = _norm_cols_any([c1,c2,c3], 3)
    t1=(request.form.get(prefix+"_disp_title_1") or sec.get("disp_titles",["","",""])[0] or "Campo 1")
    t2=(request.form.get(prefix+"_disp_title_2") or sec.get("disp_titles",["","",""])[1] or "Campo 2")
    t3=(request.form.get(prefix+"_disp_title_3") or sec.get("disp_titles",["","",""])[2] or "Campo 3")
    sec["disp_titles"] = [t1,t2,t3]

@app.route("/settings/<int:cam>", methods=["GET","POST"])
def settings_cam(cam:int):
    assert cam in (1,2)
    global cfg
    c=cfg["cameras"][cam-1]
    owners_refresh_msg=""
    visitors_refresh_msg=""
    tags_refresh_msg=""

    if request.method=="POST":
        action=(request.form.get("action") or "save").strip()

        # Dedup/gap
        c["wh_repeat_same_plate"]=_parse_bool_form(request.form.get("wh_repeat_same_plate","0"))
        c["wh_min_gap_sec"]=_clampi(request.form.get("wh_min_gap_sec", c.get("wh_min_gap_sec",0)),0,3600,c.get("wh_min_gap_sec",0))

        # Camera basics
        c["camera_mode"]=(request.form.get("camera_mode", c.get("camera_mode","mac")) or "mac").lower()
        c["camera_mac"]=(request.form.get("camera_mac", c.get("camera_mac","")) or "").upper().replace("-",":")
        c["camera_url"]=request.form.get("camera_url", c.get("camera_url",""))
        c["roi"]["enabled"]=bool(request.form.get("roi_enabled"))

        # ALPR (Valores optimizados forzados)
        c["process_every_n"] = 4       # Procesar cada 4 frames (7.5 FPS a 30 FPS de la cámara)
        c["resize_max_w"] = 800        # Resolución de red óptima
        c["alpr_topk"] = 1             # Solo necesitamos 1 candidato
        c["min_confidence"] = 0.85     # Umbral del 85% de confianza mínima
        c["idle_clear_sec"] = 2.0      # Borrar del display a los 2 segundos de inactividad

        # Pre-procesado (Forzar apagado para no saturar la CPU)
        c["pp_enabled"] = False
        c["pp_profile"] = "none"
        c["pp_clahe_clip"] = 2.0
        c["pp_sharp_strength"] = 0.55

        # Motion (Valores optimizados para evitar falsos positivos y spam)
        m = c["motion"]
        m["enabled"] = bool(request.form.get("motion_enabled"))
        try:
            m["pixel_change_pct"] = float(request.form.get("motion_pixel_change_pct", m.get("pixel_change_pct", 5.0)))
        except:
            m["pixel_change_pct"] = 5.0
        if m["enabled"]:
            m["intensity_delta"] = 25
            m["autobase_every_min"] = 10
            m["autobase_samples"] = 3
            m["autobase_interval_s"] = 1.0
            m["cooldown_s"] = 2.0

        # Gate
        c["gate_enabled"]=bool(request.form.get("gate_enabled"))
        c["gate_mode"]=(request.form.get("gate_mode", c.get("gate_mode","serial")) or "serial").lower()
        if c["gate_mode"] not in ("http","serial"): c["gate_mode"]="serial"
        c["gate_auto_on_auth"]=bool(request.form.get("gate_auto_on_auth"))
        c["gate_antispam_sec"]=_clampi(request.form.get("gate_antispam_sec", c.get("gate_antispam_sec",4)),1,600,c.get("gate_antispam_sec",4))
        c["gate_pulse_ms"]=_clampi(request.form.get("gate_pulse_ms", c.get("gate_pulse_ms",500)),20,10000,c.get("gate_pulse_ms",500))
        # HTTP
        c["gate_url"]=_norm_url(request.form.get("gate_url", c.get("gate_url","")))
        c["gate_token"]=(request.form.get("gate_token", c.get("gate_token","")) or "").strip()
        c["gate_pin"]=_clampi(request.form.get("gate_pin", c.get("gate_pin",5)),1,39,c.get("gate_pin",5))
        c["gate_active_low"]=_parse_bool_form(request.form.get("gate_active_low","0"))
        # SERIAL
        c["gate_serial_device"]=(request.form.get("gate_serial_device", c.get("gate_serial_device","")) or "").strip()
        c["gate_serial_baud"]=_clampi(request.form.get("gate_serial_baud", c.get("gate_serial_baud",115200)),1200,921600,c.get("gate_serial_baud",115200))
        c["gate_serial_gate"]=_clampi(request.form.get("gate_serial_gate", c.get("gate_serial_gate",cam)),1,8,c.get("gate_serial_gate",cam))

        # Owners & Visitors sections + webhooks
        _section_from_form("owners", c["owners"])
        c["owners"]["wh_active"]   = _pull_pair_from_form("owners_wh_active")
        c["owners"]["wh_inactive"] = _pull_pair_from_form("owners_wh_inactive")

        _section_from_form("visitors", c["visitors"])
        c["visitors"]["wh_active"]   = _pull_pair_from_form("visitors_wh_active")
        c["visitors"]["wh_inactive"] = _pull_pair_from_form("visitors_wh_inactive")

        c["wh_notfound"] = _pull_pair_from_form("plates_notfound")

        # Tags (owners only) + webhooks + format
        c["tags"]["lookup_format"] = (request.form.get("tags_lookup_format", c["tags"].get("lookup_format","physical")) or "physical").strip()
        _section_from_form("tags_owners", c["tags"]["owners"])
        c["tags"]["owners"]["wh_active"]   = _pull_pair_from_form("tags_owners_wh_active")
        c["tags"]["owners"]["wh_inactive"] = _pull_pair_from_form("tags_owners_wh_inactive")
        c["tags"]["wh_notfound"] = _pull_pair_from_form("tags_notfound")

        # Save config first
        save_cfg(cfg)

        # Actions
        if action=="copy_to_other":
            other = 2 if cam==1 else 1
            owners_refresh_msg = _copy_cam_settings(cam, other)
        elif action=="refresh_owners":
            owners_refresh_msg = download_wl(cam,"owners")
        elif action=="refresh_visitors":
            visitors_refresh_msg = download_wl(cam,"visitors")
        elif action=="refresh_tags":
            tags_refresh_msg = download_tag_wl(cam)
        else:
            owners_refresh_msg = "Guardado."

    # render
    owners=c["owners"]; visitors=c["visitors"]
    tags_lookup_format=c["tags"].get("lookup_format","physical")
    tags_owners=c["tags"]["owners"]

    return render_template_string(
        SETTINGS_CAM, cam=cam, c=c,
        owners=owners, visitors=visitors,
        owners_wh_active=_pair_block("owners_wh_active", owners.get("wh_active",{})),
        owners_wh_inactive=_pair_block("owners_wh_inactive", owners.get("wh_inactive",{})),
        visitors_wh_active=_pair_block("visitors_wh_active", visitors.get("wh_active",{})),
        visitors_wh_inactive=_pair_block("visitors_wh_inactive", visitors.get("wh_inactive",{})),
        plates_notfound=_pair_block("plates_notfound", c.get("wh_notfound",{})),
        tags_lookup_format=tags_lookup_format,
        tags_owners=tags_owners,
        tags_owners_wh_active=_pair_block("tags_owners_wh_active", tags_owners.get("wh_active",{})),
        tags_owners_wh_inactive=_pair_block("tags_owners_wh_inactive", tags_owners.get("wh_inactive",{})),
        tags_notfound=_pair_block("tags_notfound", c["tags"].get("wh_notfound",{})),
        owners_refresh_msg=owners_refresh_msg,
        visitors_refresh_msg=visitors_refresh_msg,
        tags_refresh_msg=tags_refresh_msg
    )

@app.route("/roi")
def roi_page():
    cam=1
    try: cam=int(request.args.get("cam","1"))
    except: cam=1
    cam=1 if cam==1 else 2
    return render_template_string(ROI_HTML, cam=cam)

# ---------- APIs ----------
def sh(cmd:str)->tuple[int,str]:
    try:
        out=subprocess.check_output(cmd, shell=True, stderr=subprocess.STDOUT, text=True)
        return 0,out
    except subprocess.CalledProcessError as e:
        return e.returncode, e.output

@app.route("/api/net")
def api_net():
    _,out=sh("nmcli -t -f ACTIVE,SSID,SIGNAL dev wifi | grep '^yes' || true")
    ssid=""; signal=""
    for line in out.strip().splitlines():
        parts=line.split(":")
        if parts and parts[0]=="yes":
            ssid = parts[1] if len(parts)>1 else ""
            signal = parts[2] if len(parts)>2 else ""
            break
    _,ipout=sh("hostname -I | awk '{print $1}' || true")
    return jsonify({"ssid":ssid, "signal":signal, "ip":ipout.strip()})

@app.route("/api/sys")
def api_sys():
    return jsonify({"temp_c": sys_status.get("temp_c"), "cpu_pct": sys_status.get("cpu_pct")})

@app.route("/api/gate_serial_status")
def api_gate_serial_status():
    return jsonify(gate_serial.status())

@app.route("/api/lan")
def api_lan():
    """
    Estado de conectividad por cámara.
    - MAC: resuelve IP por MAC y prueba TCP(554) y/o ping.
    - MANUAL: extrae host/port del RTSP (IP u hostname), resuelve y prueba TCP(port) y/o ping.
    """
    def _extract_host_port(rtsp_url: str):
        u = (rtsp_url or "").strip()
        if not u:
            return "", 554
        try:
            p = urlparse(u)
            host = (p.hostname or "").strip()
            port = int(p.port or 554)
            return host, port
        except Exception:
            pass
        # fallback
        try:
            x = u
            if "@" in x:
                x = x.split("@", 1)[1]
            x = x.split("/", 1)[0]
            if ":" in x:
                host, port = x.split(":", 1)
                return host.strip(), int(port.strip() or 554)
            return x.strip(), 554
        except Exception:
            return "", 554

    def _is_ip(host: str) -> bool:
        host = (host or "").strip()
        if not host:
            return False
        try:
            ipaddress.ip_address(host)
            return True
        except Exception:
            return False

    def _resolve_host(host: str) -> str:
        host = (host or "").strip()
        if not host:
            return ""
        if _is_ip(host):
            return host
        try:
            return socket.gethostbyname(host)
        except Exception:
            return ""

    def _tcp_ok(ip: str, port: int, timeout=0.6) -> bool:
        if not ip:
            return False
        try:
            with socket.create_connection((ip, int(port)), timeout=timeout):
                return True
        except Exception:
            return False

    out={}
    for cam in (1,2):
        c=cfg["cameras"][cam-1]
        url, mip, mmode = materialize_url(c)
        
        if "{CAM_IP}" in (url or ""):
            # Sigue sin resolver MAC
            out[f"cam{cam}"]={"ok":False,"ip":"","host":"","mode":mmode,"port":554,"tcp":False}
            continue
            
        host, port = _extract_host_port(url)
        ip=_resolve_host(host) if host else ""
        tcp=_tcp_ok(ip, port, timeout=0.6) if ip else False
        ok = tcp or (bool(ip) and _ping(ip,1))
        out[f"cam{cam}"]={"ok":ok,"ip":(ip or ""),"host":(host or ""),"mode":mmode,"port":int(port or 554),"tcp":tcp}

    return jsonify(out)



@app.route("/api/motion")
def api_motion():
    out={}
    for cam in (1,2):
        st=motion[cam-1]
        q = send_mgr[cam-1].q
        out[f"cam{cam}"]={
            "active": bool(st.active),
            "ratio": float(st.last_ratio),
            "queue": {"pending": q.qsize(), "dropped": send_mgr[cam-1].dropped, "sent": send_mgr[cam-1].sent}
        }
    out["gate_serial"]=gate_serial.status()
    return jsonify(out)

@app.route("/snapshot.jpg")
def snapshot():
    cam=1
    try: cam=int(request.args.get("cam","1"))
    except: cam=1
    cam=1 if cam==1 else 2
    fr=grab[cam-1].get()
    if fr is None: return ("No frame",503,{"Content-Type":"text/plain"})
    try: w=int(request.args.get("w","0"))
    except: w=0
    fr2=fr
    if w>32:
        h,wi=fr2.shape[:2]; tw=min(w,wi); th=int(h*(tw/float(wi)))
        fr2=cv2.resize(fr2,(tw,th),interpolation=cv2.INTER_AREA)
    ok,buf=cv2.imencode(".jpg", fr2, [cv2.IMWRITE_JPEG_QUALITY,92])
    if not ok: return ("Encode error",500,{"Content-Type":"text/plain"})
    r=Response(buf.tobytes(), mimetype="image/jpeg")
    r.headers["Cache-Control"]="no-store, no-cache, must-revalidate, max-age=0, no-transform"
    return r




@app.route("/snapshot_alpr.jpg")
def snapshot_alpr():
    """
    Snapshot SOLO para vista ROI:
    - Recorta ROI (si enabled)
    - Aplica preprocesado (si existe y está habilitado en Settings)
    - NO toca stream/snapshot normal ni webhooks
    """
    cam = 1
    try:
        cam = int(request.args.get("cam", "1"))
    except Exception:
        cam = 1
    cam = 1 if cam == 1 else 2

    fr = grab[cam-1].get()
    if fr is None:
        return ("No frame", 503, {"Content-Type": "text/plain"})

    # ROI
    try:
        fr_roi = _apply_roi(cam, fr)
    except Exception:
        fr_roi = fr

    # Preprocesado defensivo
    fr_alpr = fr_roi
    try:
        fn = globals().get("_preprocess_for_alpr")
        if callable(fn):
            fr_alpr = fn(cam, fr_roi)
    except Exception:
        fr_alpr = fr_roi

    # Resize opcional
    try:
        w = int(request.args.get("w", "0"))
    except Exception:
        w = 0
    fr2 = fr_alpr
    if w and w > 32:
        h, wi = fr2.shape[:2]
        tw = min(w, wi)
        th = int(max(24, h * (tw / float(wi))))
        try:
            fr2 = cv2.resize(fr2, (tw, th), interpolation=cv2.INTER_AREA)
        except Exception:
            pass

    ok, buf = cv2.imencode(".jpg", fr2, [cv2.IMWRITE_JPEG_QUALITY, 75])
    if not ok:
        return ("Encode error", 500, {"Content-Type": "text/plain"})
    r = Response(buf.tobytes(), mimetype="image/jpeg")
    r.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0, no-transform"
    return r
@app.route("/snapshot_pre.jpg")
def snapshot_pre():
    cam=1
    try: cam=int(request.args.get("cam","1"))
    except: cam=1
    cam=1 if cam==1 else 2

    fr=grab[cam-1].get()
    if fr is None: 
        return ("No frame",503,{"Content-Type":"text/plain"})

    # Esto muestra EXACTAMENTE lo que ve ALPR: ROI + preprocesado (si está habilitado)
    try:
        fr_roi=_apply_roi(cam, fr)
    except Exception:
        fr_roi=fr

    try:
        fr_alpr=_preprocess_for_alpr(cam, fr_roi)  # si está OFF, debe regresar la misma imagen o muy similar
    except Exception:
        fr_alpr=fr_roi

    try: 
        w=int(request.args.get("w","0"))
    except: 
        w=0

    fr2=fr_alpr
    if w>32 and fr2 is not None:
        try:
            h,wi=fr2.shape[:2]
            tw=min(w,wi); th=int(h*(tw/float(wi)))
            fr2=cv2.resize(fr2,(tw,th),interpolation=cv2.INTER_AREA)
        except Exception:
            pass

    ok,buf=cv2.imencode(".jpg", fr2, [cv2.IMWRITE_JPEG_QUALITY,75])
    if not ok: 
        return ("Encode error",500,{"Content-Type":"text/plain"})
    r=Response(buf.tobytes(), mimetype="image/jpeg")
    r.headers["Cache-Control"]="no-store, no-cache, must-revalidate, max-age=0, no-transform"
    return r

@app.route("/api/roi_get")
def api_roi_get():
    cam=1
    try: cam=int(request.args.get("cam","1"))
    except: cam=1
    cam=1 if cam==1 else 2
    r = cfg["cameras"][cam-1].get("roi", {"enabled":False,"x":0,"y":0,"w":1,"h":1})
    return jsonify({"cam":cam,"roi":r})

@app.route("/api/roi_save", methods=["POST"])
def api_roi_save():
    if not _check_token(): return jsonify({"error":"unauthorized"}), 401
    cam=1
    try: cam=int(request.args.get("cam","1"))
    except: cam=1
    cam=1 if cam==1 else 2
    body = request.get_json(force=True, silent=True) or {}
    x=float(body.get("x",0)); y=float(body.get("y",0))
    w=float(body.get("w",1)); h=float(body.get("h",1))
    en=bool(body.get("enabled", True))
    x=max(0.0,min(1.0,x)); y=max(0.0,min(1.0,y))
    w=max(0.0,min(1.0,w)); h=max(0.0,min(1.0,h))
    if x+w>1.0: w=1.0-x
    if y+h>1.0: h=1.0-y
    cfg["cameras"][cam-1]["roi"]={"enabled":en,"x":x,"y":y,"w":w,"h":h}
    save_cfg(cfg)
    motion[cam-1].baseline=None
    return jsonify({"ok":True,"message":"ROI guardado","roi":cfg["cameras"][cam-1]["roi"]})

@app.route("/api/roi_clear", methods=["POST"])
def api_roi_clear():
    if not _check_token(): return jsonify({"error":"unauthorized"}), 401
    cam=1
    try: cam=int(request.args.get("cam","1"))
    except: cam=1
    cam=1 if cam==1 else 2
    cfg["cameras"][cam-1]["roi"]={"enabled":False,"x":0.0,"y":0.0,"w":1.0,"h":1.0}
    save_cfg(cfg)
    motion[cam-1].baseline=None
    return jsonify({"ok":True,"message":"ROI limpiado y deshabilitado"})

@app.route("/api/status")
def api_status():
    cam=1
    try: cam=int(request.args.get("cam","1"))
    except: cam=1
    cam=1 if cam==1 else 2
    cdict=cfg["cameras"][cam-1]
    with slock[cam-1]:
        st=states[cam-1].copy()
        tgs=tag_states[cam-1].copy()

    now=time.time()
    idle=float(cdict.get("idle_clear_sec",1.5))
    hold=float(cdict.get("latch_hold_sec",30.0))

    if (not st["plate"]) or ((now-(st["ts"] or 0))>hold):
        st["plate"]=""; st["conf"]=0.0; st["auth"]=False; st["display"]=["","",""]; st["user_type"]="NONE"; st["cat"]="NONE"
    if (not tgs["tag"]) or ((now-(tgs["ts"] or 0))>hold):
        tgs["tag"]=""; tgs["auth"]=False; tgs["cat"]="NONE"; tgs["user_type"]="NONE"; tgs["fields"]=["","",""]

    return jsonify({
        "cam":cam,
        "plate":st["plate"],
        "conf":st["conf"],
        "ts":st["ts"],
        "category":st["cat"],
        "user_type":st["user_type"],
        "fields":st["display"],
        "idle":idle,
        "hold":hold,
        "tag":tgs["tag"],
        "tag_ts":tgs["ts"],
        "tag_cat":tgs["cat"],
        "tag_fields":tgs["fields"]
    })

@app.route("/api/gate_open", methods=["POST"])
def api_gate_open():
    if not _check_token(): return jsonify({"ok":False,"error":"unauthorized"}), 401
    cam=1
    try: cam=int(request.args.get("cam","1"))
    except: cam=1
    cam=1 if cam==1 else 2
    ok,msg=gate_fire(cam)
    return jsonify({"ok":ok,"error":(None if ok else msg)}), (200 if ok else 500)

@app.route("/api/wl_refresh", methods=["POST"])
def api_wl_refresh():
    if not _check_token(): return jsonify({"ok":False,"error":"unauthorized"}), 401
    cam=_clampi(request.args.get("cam","1"),1,2,1)
    kind=(request.args.get("kind","owners") or "owners").lower()
    if kind not in ("owners","visitors"):
        return jsonify({"ok":False,"error":"kind inválido"}), 400
    msg=download_wl(cam,kind)
    return jsonify({"ok":True,"message":msg})

@app.route("/api/tag_wl_refresh", methods=["POST"])
def api_tag_wl_refresh():
    if not _check_token(): return jsonify({"ok":False,"error":"unauthorized"}), 401
    cam=_clampi(request.args.get("cam","1"),1,2,1)
    msg=download_tag_wl(cam)
    return jsonify({"ok":True,"message":msg})

@app.route("/api/tag_event", methods=["POST"])
def api_tag_event():
    body = request.get_json(force=True, silent=True) or {}
    cam = _clampi(body.get("cam",1),1,2,1)

    fmt = (cfg["cameras"][cam-1]["tags"].get("lookup_format","physical") or "physical").lower()
    physical = (body.get("tag_physical") or "").strip().upper()
    internal = (body.get("tag_internal_hex") or "").strip().upper()
    key = internal if fmt=="internal_hex" else physical
    pkey = canon_plate(key)

    user_type="NONE"; row=None; auth=False
    disp_vals=["","",""]; titles=["Folio","Nombre","Telefono"]
    cat="NOTFOUND"

    if pkey:
        user_type,row = lookup_tag_row(cam, pkey)

    ccam=cfg["cameras"][cam-1]
    if user_type=="PROPIETARIO":
        sec=ccam["tags"]["owners"]
        auth=is_active_from_row(sec,row)
        disp_vals=_extract_fields(row, sec.get("disp_cols"))
        titles=sec.get("disp_titles",titles)
        pair=sec["wh_active"] if auth else sec["wh_inactive"]
        cat="ACTIVE" if auth else "INACTIVE"
    else:
        pair=ccam["tags"]["wh_notfound"]
        cat="NOTFOUND"

    # Gate auto
    if auth and ccam.get("gate_enabled",False) and ccam.get("gate_auto_on_auth",False):
        if gate_can_fire(cam): gate_fire(cam)

    with slock[cam-1]:
        tag_states[cam-1]["tag"] = (physical or internal or "")
        tag_states[cam-1]["ts"]  = time.time()
        tag_states[cam-1]["auth"]=bool(auth)
        tag_states[cam-1]["cat"]=cat
        tag_states[cam-1]["user_type"]=user_type
        tag_states[cam-1]["fields"]=disp_vals

    log_event("TAG", cam, pkey, 1.00, cat, user_type, auth, disp_vals)

    # Webhooks tags
    if user_type=="PROPIETARIO":
        enqueue_webhooks(cam, cat, pair, user_type, "Tag", pkey, disp_vals, titles)
    else:
        enqueue_webhooks(cam, "NOTFOUND", pair, "NoFound", "Tag", pkey, ["","",""], ["Folio","Nombre","Telefono"])

    return jsonify({"ok":True,"active":bool(auth),"category":cat,"user_type":user_type})


@app.route("/api/alpr_debug")
def api_alpr_debug():
    cam=1
    try:
        cam=int(request.args.get("cam","1"))
    except:
        cam=1
    cam=1 if cam==1 else 2

    fr=grab[cam-1].get()
    if fr is None:
        return jsonify({"ok":False,"error":"no-frame","cam":cam}), 503

    try:
        fr_roi=_apply_roi(cam, fr)
    except Exception as e:
        return jsonify({"ok":False,"error":f"roi-error: {e}","cam":cam}), 500

    try:
        fr_alpr=_preprocess_for_alpr(cam, fr_roi)
    except Exception as e:
        return jsonify({"ok":False,"error":f"preprocess-error: {e}","cam":cam}), 500

    try:
        results=run_alpr(fr_alpr, cfg["cameras"][cam-1]["resize_max_w"], topk=cfg["cameras"][cam-1]["alpr_topk"])
    except Exception as e:
        return jsonify({"ok":False,"error":f"run_alpr-error: {e}","cam":cam}), 500

    out=[]
    for t,c in results:
        try:
            out.append({"text":str(t), "conf":float(c)})
        except Exception:
            out.append({"text":str(t), "conf":0.0})

    return jsonify({
        "ok":True,
        "cam":cam,
        "frame_shape": (list(fr.shape) if fr is not None else None),
        "roi_shape": (list(fr_roi.shape) if fr_roi is not None else None),
        "alpr_shape": (list(fr_alpr.shape) if fr_alpr is not None else None),
        "count": len(out),
        "results": out,
        "cfg": {
            "camera_mode": cfg["cameras"][cam-1].get("camera_mode"),
            "resize_max_w": cfg["cameras"][cam-1].get("resize_max_w"),
            "min_confidence": cfg["cameras"][cam-1].get("min_confidence"),
            "roi_enabled": cfg["cameras"][cam-1].get("roi",{}).get("enabled"),
            "motion_enabled": cfg["cameras"][cam-1].get("motion",{}).get("enabled"),
            "pp_enabled": cfg["cameras"][cam-1].get("pp_enabled"),
        }
    })

@app.route("/healthz")
def healthz():
    ok1=grab[0].get() is not None
    ok2=grab[1].get() is not None
    return (f"CAM1:{'OK' if ok1 else 'NO'} CAM2:{'OK' if ok2 else 'NO'}", (200 if (ok1 or ok2) else 503))

# ========== WiFi Manager ==========
WIFI_HTML = """<!doctype html><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>WiFi Manager</title>
<style>
 body{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;margin:0;padding:20px;background:#f5f6fa;color:#333}
 .card{background:#fff;border-radius:12px;padding:20px;max-width:600px;margin:0 auto;box-shadow:0 2px 8px rgba(0,0,0,0.1)}
 h2{margin-top:0;font-weight:600;color:#111}
 p{line-height:1.5;color:#555}
 .row{display:flex;justify-content:space-between;padding:12px 0;border-bottom:1px solid #eee;align-items:center;flex-wrap:wrap;gap:10px}
 .row:last-child{border-bottom:none}
 .btn{padding:10px 18px;background:#007bff;color:#fff;border:none;border-radius:6px;cursor:pointer;font-weight:600;font-size:14px;transition:0.2s}
 .btn:hover{background:#0056b3}
 .btn:disabled{background:#ccc;cursor:not-allowed}
 input[type="password"]{padding:10px;border:1px solid #ccc;border-radius:6px;width:150px;font-size:14px}
 .msg{margin-top:15px;color:#d9534f;font-weight:bold;padding:10px;border-radius:6px;background:#fdf2f2;display:none}
 .msg.active{display:block}
 .msg.ok{color:#155724;background:#d4edda}
 .controls{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:20px}
 .controls a.btn{background:#6c757d;text-decoration:none;display:inline-block}
 .controls a.btn:hover{background:#5a6268}
</style>
<div class="card">
  <h2>📡 Gestor de Redes WiFi</h2>
  <p>Escanea y conecta la Raspberry Pi a redes inalámbricas. Las redes guardadas se recordarán automáticamente en el futuro, ideal para configurarla en el laboratorio antes de instalar en campo.</p>
  
  <div class="controls">
    <button class="btn" id="scanBtn" onclick="scan()">🔄 Escanear Redes</button>
    <a class="btn" href="/">⬅ Volver al Portal</a>
  </div>
  
  <div id="status" class="msg"></div>
  <div id="list" style="margin-top:20px"></div>
  
  <div style="margin-top:30px;padding-top:20px;border-top:1px solid #eee">
    <h3 style="margin-top:0">Agregar Red Manualmente</h3>
    <p style="font-size:14px;color:#666">Usa esta opción para configurar una red oculta o una red que no aparece en el escaneo (ej. la red del cliente final donde se instalará el equipo).</p>
    <div style="display:flex;gap:10px;flex-wrap:wrap">
      <input type="text" id="manual_ssid" placeholder="Nombre de la red (SSID)" style="padding:10px;border:1px solid #ccc;border-radius:6px;flex:1;min-width:150px">
      <input type="password" id="manual_pw" placeholder="Contraseña (opcional)" style="padding:10px;border:1px solid #ccc;border-radius:6px;flex:1;min-width:150px">
      <button class="btn" onclick="connectManual()">Guardar y Conectar</button>
    </div>
  </div>
</div>

<script>
function showMsg(txt, isOk=false) {
  const el = document.getElementById('status');
  el.textContent = txt;
  el.className = 'msg active ' + (isOk ? 'ok' : '');
}

async function scan(){
  const btn = document.getElementById('scanBtn');
  const lst = document.getElementById('list');
  btn.disabled = true;
  showMsg("Escaneando redes (puede tardar unos segundos)...");
  lst.innerHTML = "";
  
  try {
    const r = await fetch('/api/wifi/scan');
    const data = await r.json();
    if(!data.ok) throw new Error(data.error);
    
    if(data.networks.length === 0){
      showMsg("No se encontraron redes WiFi cercanas.", false);
    } else {
      document.getElementById('status').className = "msg"; // Hide msg
      data.networks.forEach(nw => {
        if(!nw.ssid) return;
        const row = document.createElement('div');
        row.className = "row";
        row.innerHTML = `
          <div style="flex:1;min-width:200px">
            <strong style="font-size:16px;color:#000">${nw.ssid}</strong><br>
            <small style="color:#666">📶 Señal: ${nw.signal}% &nbsp;•&nbsp; 🔒 Seg: ${nw.security}</small>
          </div>
          <div style="display:flex;gap:8px">
            <input type="password" id="pw_${btoa(nw.ssid).replace(/=/g,'')}" placeholder="Contraseña">
            <button class="btn" onclick="connect('${nw.ssid}', '${btoa(nw.ssid).replace(/=/g,'')}')">Conectar</button>
          </div>
        `;
        lst.appendChild(row);
      });
    }
  } catch(e) {
    showMsg("Error: " + e.message, false);
  } finally {
    btn.disabled = false;
  }
}

async function connect(ssid, id){
  const pwEl = document.getElementById('pw_'+id);
  const pw = pwEl.value;
  showMsg("Conectando a '" + ssid + "'... Esto puede demorar.", false);
  
  try {
    const r = await fetch('/api/wifi/connect', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ssid: ssid, password: pw})
    });
    const data = await r.json();
    if(data.ok){
      showMsg("¡Conectado exitosamente a " + ssid + "!", true);
      pwEl.value = '';
    } else {
      showMsg("Error al conectar: " + (data.error || "Revisa la contraseña"), false);
    }
  } catch(e) {
    showMsg("Error de red: " + e.message, false);
  }
}

async function connectManual(){
  const ssid = document.getElementById('manual_ssid').value.trim();
  if(!ssid){
    showMsg("Ingresa el nombre de la red (SSID)", false);
    return;
  }
  const pw = document.getElementById('manual_pw').value;
  showMsg("Guardando perfil para '" + ssid + "'...", false);
  
  try {
    const r = await fetch('/api/wifi/connect', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ssid: ssid, password: pw})
    });
    const data = await r.json();
    if(data.ok){
      showMsg("¡Red " + ssid + " guardada exitosamente!", true);
      document.getElementById('manual_ssid').value = '';
      document.getElementById('manual_pw').value = '';
    } else {
      showMsg("Atención: " + (data.error || "Fallo al configurar"), false);
      // Even if nmcli fails (e.g. out of range), the profile MIGHT have been created, 
      // but nmcli connect fails when out of range. That's fine for our use case.
    }
  } catch(e) {
    showMsg("Error de red: " + e.message, false);
  }
}
</script>
"""

@app.route("/wifi")
def wifi_page():
    return render_template_string(WIFI_HTML)

@app.route("/api/wifi/scan")
def api_wifi_scan():
    code, out = sh("nmcli -t -f SSID,SIGNAL,SECURITY dev wifi list")
    if code != 0:
        return jsonify({"ok":False, "error": out})
    seen = set()
    nets = []
    for line in out.splitlines():
        parts = line.split(":")
        if len(parts) >= 3:
            ssid = parts[0].strip()
            # ignorar redes ocultas o ya vistas
            if not ssid or ssid in seen or ssid.startswith("--"): 
                continue
            seen.add(ssid)
            nets.append({
                "ssid": ssid,
                "signal": parts[1].strip(),
                "security": parts[2].strip()
            })
    return jsonify({"ok":True, "networks": nets})

@app.route("/api/wifi/connect", methods=["POST"])
def api_wifi_connect():
    data = request.get_json() or {}
    ssid = data.get("ssid", "").replace("'", "")
    pw = data.get("password", "").replace("'", "")
    if not ssid:
        return jsonify({"ok":False, "error":"SSID vacío"})
    
    # Intenta borrar conexión previa para evitar conflictos si cambió la clave
    sh(f"nmcli connection delete '{ssid}'")
    
    if pw:
        cmd = f"nmcli dev wifi connect '{ssid}' password '{pw}'"
    else:
        cmd = f"nmcli dev wifi connect '{ssid}'"
        
    code, out = sh(cmd)
    return jsonify({"ok":(code==0), "error":out if code!=0 else ""})

# ========== Logs & Diagnóstico ==========
@app.route("/logs")
def view_logs():
    import csv
    logs = []
    headers = ["Fecha/Hora", "Tipo", "Cámara", "Identificador", "Confianza", "Categoría", "Tipo Usuario", "Autorización", "Detalles"]
    try:
        if os.path.exists(LOG_FILE):
            with open(LOG_FILE, "r", encoding="utf-8") as f:
                reader = csv.reader(f)
                rows = list(reader)
                if len(rows) > 1:
                    headers = rows[0]
                    logs = rows[1:][-300:]
                    logs.reverse()
    except Exception as e:
        print("Error leyendo logs:", e)

    now = time.time()
    thread_status = []
    for name, ts in sorted(thread_heartbeats.items()):
        diff = now - ts
        status = "ACTIVO" if diff < 45 else "INACTIVO/CONGELADO"
        color = "#10b981" if diff < 45 else "#ef4444"
        thread_status.append({
            "name": name,
            "last_seen": f"{diff:.1f}s atrás",
            "status": status,
            "color": color
        })

    html = """
    <!DOCTYPE html>
    <html>
    <head>
      <meta charset="utf-8">
      <title>Historial de Eventos - Comunito Portal</title>
      <style>
        body{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;margin:24px;background:#f8fafc;color:#1e293b}
        h1{margin:0 0 12px;font-weight:800;letter-spacing:-0.5px;color:#0f172a;font-size:26px}
        .btn{padding:8px 14px;border:none;border-radius:8px;background:#cbd5e1;cursor:pointer;font-weight:600;font-size:13px;color:#334155;transition:all 0.2s;text-decoration:none;display:inline-flex;align-items:center;justify-content:center;margin-right:8px}
        .btn:hover{background:#94a3b8;transform:translateY(-1px)}
        .btn-primary{background:#2563eb;color:#fff}
        .btn-primary:hover{background:#1d4ed8}
        .btn-danger{background:#ef4444;color:#fff}
        .btn-danger:hover{background:#dc2626}
        .card{border:1px solid #e2e8f0;border-radius:16px;padding:20px;background:#fff;box-shadow:0 4px 6px -1px rgba(0,0,0,0.05);margin-bottom:20px}
        .card h3{margin:0 0 12px 0;font-size:16px;color:#0f172a;border-bottom:1px solid #f1f5f9;padding-bottom:8px}
        table{width:100%;border-collapse:collapse;margin-top:10px;font-size:13px}
        th,td{padding:10px 12px;text-align:left;border-bottom:1px solid #f1f5f9}
        th{background:#f8fafc;font-weight:700;color:#475569}
        tr:hover{background:#f8fafc}
        .badge{padding:3px 8px;border-radius:6px;font-size:11px;font-weight:700;text-transform:uppercase}
        .badge-active{background:#dcfce7;color:#15803d}
        .badge-inactive{background:#fee2e2;color:#b91c1c}
        .badge-notfound{background:#f1f5f9;color:#475569}
        .badge-auth{background:#dcfce7;color:#15803d}
        .badge-denied{background:#fee2e2;color:#b91c1c}
        .status-dot{display:inline-block;width:8px;height:8px;border-radius:50%;margin-right:6px}
      </style>
    </head>
    <body>
      <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:20px">
        <h1>📝 Historial de Operación y Diagnóstico</h1>
        <div>
          <a class="btn btn-primary" href="/">🏠 Volver al Inicio</a>
          <a class="btn" href="/logs/download">📥 Descargar CSV Completo</a>
          <a class="btn" href="/crash/view">⚠️ Ver Log de Crashes</a>
          <a class="btn btn-danger" href="/logs/clear" onclick="return confirm('¿Seguro que deseas borrar el historial?')">🗑️ Borrar Historial</a>
        </div>
      </div>

      <div class="card">
        <h3>⚡ Estado de Hilos del Sistema (Watchdog)</h3>
        <div style="display:flex;flex-wrap:wrap;gap:16px">
          {% for th in thread_status %}
            <div style="background:#f8fafc;padding:8px 12px;border-radius:8px;border:1px solid #e2e8f0;font-size:12px;min-width:180px">
              <span class="status-dot" style="background:{{th.color}}"></span>
              <b>{{th.name}}</b><br>
              <span class="muted" style="color:#64748b">Estado: {{th.status}} ({{th.last_seen}})</span>
            </div>
          {% endfor %}
        </div>
      </div>

      <div class="card">
        <h3>🚗 Últimos 300 Eventos Registrados</h3>
        <table>
          <thead>
            <tr>
              {% for h in headers %}
                <th>{{h}}</th>
              {% endfor %}
            </tr>
          </thead>
          <tbody>
            {% for row in logs %}
              <tr>
                {% for cell in row %}
                  <td>
                    {% if cell == 'ACTIVE' or cell == 'PROPIETARIO' or cell == 'VISITA' %}
                      <span class="badge badge-active">{{cell}}</span>
                    {% elif cell == 'INACTIVE' %}
                      <span class="badge badge-inactive">{{cell}}</span>
                    {% elif cell == 'NOTFOUND' or cell == 'NONE' or cell == 'NoFound' %}
                      <span class="badge badge-notfound">{{cell}}</span>
                    {% elif cell == 'AUTORIZADO' %}
                      <span class="badge badge-auth">{{cell}}</span>
                    {% elif cell == 'DENEGADO' %}
                      <span class="badge badge-denied">{{cell}}</span>
                    {% else %}
                      {{cell}}
                    {% endif %}
                  </td>
                {% endfor %}
              </tr>
            {% else %}
              <tr>
                <td colspan="9" style="text-align:center;color:#64748b;padding:20px">No hay eventos registrados en el log local.</td>
              </tr>
            {% endfor %}
          </tbody>
        </table>
      </div>
    </body>
    </html>
    """
    return render_template_string(html, headers=headers, logs=logs, thread_status=thread_status)

@app.route("/logs/download")
def download_logs():
    if os.path.exists(LOG_FILE):
        return send_file(LOG_FILE, as_attachment=True, download_name="portal_history.csv")
    return "No hay archivo de log disponible", 404

@app.route("/logs/clear")
def clear_logs():
    try:
        if os.path.exists(LOG_FILE):
            os.remove(LOG_FILE)
        return redirect("/logs")
    except Exception as e:
        return f"Error borrando archivo de logs: {e}", 500

@app.route("/crash/view")
def view_crash_log():
    content = "No se ha registrado ningún crash en el sistema."
    try:
        if os.path.exists(CRASH_LOG):
            with open(CRASH_LOG, "r", encoding="utf-8") as f:
                content = f.read()
    except Exception as e:
        content = f"Error leyendo log de crashes: {e}"
        
    html = """
    <!DOCTYPE html>
    <html>
    <head>
      <meta charset="utf-8">
      <title>Log de Crashes - Comunito Portal</title>
      <style>
        body{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;margin:24px;background:#f8fafc;color:#1e293b}
        h1{margin:0 0 12px;font-weight:800;letter-spacing:-0.5px;color:#0f172a;font-size:26px}
        .btn{padding:8px 14px;border:none;border-radius:8px;background:#cbd5e1;cursor:pointer;font-weight:600;font-size:13px;color:#334155;transition:all 0.2s;text-decoration:none;display:inline-flex;align-items:center;justify-content:center}
        .btn:hover{background:#94a3b8;transform:translateY(-1px)}
        .btn-primary{background:#2563eb;color:#fff}
        .btn-primary:hover{background:#1d4ed8}
        .btn-danger{background:#ef4444;color:#fff}
        .btn-danger:hover{background:#dc2626}
        pre{background:#0f172a;color:#cbd5e1;padding:20px;border-radius:12px;font-family:"SF Mono",ui-monospace,monospace;font-size:13px;overflow-x:auto;box-shadow:inset 0 2px 4px rgba(0,0,0,0.1);max-height:600px}
      </style>
    </head>
    <body>
      <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:20px">
        <h1>⚠️ Log de Diagnóstico de Crashes y Congelamientos</h1>
        <div>
          <a class="btn btn-primary" href="/logs">📋 Volver a Logs</a>
          <a class="btn" href="/crash/download">📥 Descargar Log</a>
          <a class="btn btn-danger" href="/crash/clear" onclick="return confirm('¿Seguro que deseas borrar el registro de crashes?')">🗑️ Limpiar Log</a>
        </div>
      </div>
      <pre>{{content}}</pre>
    </body>
    </html>
    """
    return render_template_string(html, content=content)

@app.route("/crash/download")
def download_crash_log():
    if os.path.exists(CRASH_LOG):
        return send_file(CRASH_LOG, as_attachment=True, download_name="crash.log")
    return "No hay archivo de crash disponible", 404

@app.route("/crash/clear")
def clear_crash_log():
    try:
        if os.path.exists(CRASH_LOG):
            os.remove(CRASH_LOG)
        return redirect("/crash/view")
    except Exception as e:
        return f"Error borrando archivo de logs de crash: {e}", 500

def notify_watchdog():
    sock_path = os.environ.get("NOTIFY_SOCKET")
    if not sock_path:
        return
    if sock_path.startswith("@"):
        sock_path = "\0" + sock_path[1:]
    try:
        with socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM) as s:
            s.connect(sock_path)
            s.sendall(b"WATCHDOG=1")
    except Exception:
        pass

def _watchdog_thread():
    time.sleep(10)
    for k in list(thread_heartbeats.keys()):
        thread_heartbeats[k] = time.time()
        
    while True:
        time.sleep(5)
        now = time.time()
        stuck_threads = []
        for name, ts in thread_heartbeats.items():
            if now - ts > 45:
                stuck_threads.append(name)
        
        if stuck_threads:
            try:
                with open(CRASH_LOG, "a", encoding="utf-8") as f:
                    f.write(f"\n--- WATCHDOG WARNING AT {_iso_now_early()} ---\n")
                    f.write(f"Hilos bloqueados o inactivos: {', '.join(stuck_threads)}\n")
                    f.write("No se enviará el ping de Watchdog a systemd para forzar el reinicio.\n")
                    f.flush()
                    os.fsync(f.fileno())
            except Exception:
                pass
            print(f"[WATCHDOG] Hilos bloqueados: {stuck_threads}. Forzando reinicio por inactividad.")
        else:
            notify_watchdog()

# ----- Threads -----
_load_wl_from_cache()
for i in (1,2):
    threading.Thread(target=_alpr_loop, args=(i,), daemon=True).start()
    threading.Thread(target=_motion_loop, args=(i,), daemon=True).start()
threading.Thread(target=_auto_refresh_loop, daemon=True).start()
threading.Thread(target=_sysmon_loop, daemon=True).start()
threading.Thread(target=_heartbeat_scheduler_loop, daemon=True).start()
threading.Thread(target=_watchdog_thread, daemon=True).start()

if __name__=="__main__":
    os.environ["TZ"]="America/Mexico_City"
    try:
        from waitress import serve
        serve(app, host="0.0.0.0", port=5000, threads=8)
    except Exception:
        app.run(host="0.0.0.0", port=5000, threaded=True)
