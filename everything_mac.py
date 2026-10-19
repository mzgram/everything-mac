#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Everything (Mac) - dosya ve klasörleri anında bulun.

voidtools Everything'in Mac için, sıfırdan yazılmış işlevsel bir benzeri.
Yalnızca Python standart kütüphanesini kullanır (tkinter + sqlite3).
İsteğe bağlı: `pip3 install watchdog` -> gerçek zamanlı güncelleme (FSEvents).

Çalıştırma:   python3 everything_mac.py
Arama sözdizimi için programda Yardım > Arama Sözdizimi menüsüne bakın.
"""

import csv
import fnmatch
import json
import os
import queue
import re
import shutil
import sqlite3
import subprocess
import sys
import threading
import time
import unicodedata
from collections import namedtuple
from datetime import datetime, timedelta
from functools import lru_cache

try:
    import tkinter as tk
    import tkinter.font as tkfont
    from tkinter import filedialog, messagebox, simpledialog, ttk
except ImportError:  # Homebrew Python'da: brew install python-tk
    tk = None
    tkfont = None

APP_NAME = "EverythingMac"
APP_VERSION = "2.0"
SCHEMA_VERSION = 3
RESULT_LIMIT = 2000          # ekranda gösterilecek en fazla satır
POLL_SECONDS = 60            # watchdog yoksa periyodik tarama aralığı
BATCH_ROWS = 5000            # bu kadar satırda bir commit (sonuçlar canlı görünsün)

SKIP_NAMES = {".Spotlight-V100", ".fseventsd", ".Trashes",
              ".DocumentRevisions-V100", ".TemporaryItems", ".vol",
              "$RECYCLE.BIN", "System Volume Information", ".DS_Store", ".localized"}
# macOS'ta Finder'ın tek dosya gibi gösterdiği paketler (içleri varsayılan olarak indekslenmez)
PACKAGE_EXTS = (".app", ".photoslibrary", ".imovielibrary", ".fcpbundle", ".tvlibrary",
                ".musiclibrary", ".bundle", ".framework", ".plugin", ".kext", ".xcodeproj")
VOLUMES_DIR = "/Volumes"
_ismount = os.path.ismount
SKIP_PATHS = {"/System/Volumes", "/dev", "/private/var/vm", "/proc"}

# Sonuç listesindeki sütunlar: id -> (başlık, varsayılan genişlik, hizalama)
COLUMNS = {
    "name": ("Ad", 300, "w"),
    "path": ("Yol", 420, "w"),
    "size": ("Boyut", 90, "e"),
    "ext": ("Uzantı", 70, "w"),
    "type": ("Tür", 130, "w"),
    "date": ("Değiştirilme tarihi", 150, "w"),
    "btime": ("Oluşturulma tarihi", 150, "w"),
}
COLUMN_ORDER = list(COLUMNS)


def set_result_limit(n):
    global RESULT_LIMIT
    RESULT_LIMIT = max(100, int(n))


# --------------------------------------------------------------------------
# Yardımcılar
# --------------------------------------------------------------------------

def data_dir():
    override = os.environ.get("EVERYTHING_MAC_DATA")
    if override:
        base = override
    elif sys.platform == "darwin":
        base = os.path.join(os.path.expanduser("~/Library/Application Support"), APP_NAME)
    elif sys.platform == "win32":
        base = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), APP_NAME)
    else:
        base = os.path.join(os.path.expanduser("~/.local/share"), APP_NAME)
    os.makedirs(base, exist_ok=True)
    return base


_TR_MAP = str.maketrans({"İ": "i", "ı": "i"})


def fold(s):
    """Arama anahtarı: büyük/küçük harf ve aksan fark etmez (ş=s, ğ=g, ı=i, İ=i ...).
    macOS dosya adları sıklıkla ayrışık (NFD) gelir; bu da onu normalleştirir."""
    if s.isascii():
        return s.lower()
    s = unicodedata.normalize("NFD", s.translate(_TR_MAP))
    s = "".join(ch for ch in s if not unicodedata.combining(ch))
    return unicodedata.normalize("NFC", s).lower()


def fold_keep(s):
    """Aksanları koruyan anahtar ('Aksanları eşleştir' seçeneği için)."""
    return unicodedata.normalize("NFC", s.replace("İ", "i")).lower()


def fmt_int(n):
    return f"{n:,}".replace(",", ".")


def fmt_size(n):
    if n < 1024:
        return f"{n} B"
    for unit in ("KB", "MB", "GB", "TB"):
        n /= 1024.0
        if n < 1024 or unit == "TB":
            return (f"{n:.1f}" if n < 10 else f"{n:.0f}").replace(".", ",") + " " + unit


def fmt_date(ts):
    try:
        return datetime.fromtimestamp(ts).strftime("%d.%m.%Y %H:%M")
    except (OverflowError, OSError, ValueError):
        return ""


DEFAULT_HOME = {"search": "", "filter": "Hepsi", "sort": "name", "desc": False,
                "match_case": False, "match_path": False, "regex": False,
                "whole_word": False, "diacritics": False}


def default_config():
    home = os.path.expanduser("~")
    return {
        "roots": [home], "excludes": [os.path.join(home, "Library")],
        "auto_external": True, "ignored_volumes": [],
        "skip_packages": True, "fda_warned": False,
        "exclude_patterns": [], "exclude_hidden": False,
        "result_limit": 2000, "font_size": 13,
        "show_status": True, "always_on_top": False,
        "search_as_you_type": True, "save_history": True, "history": [],
        "columns": ["name", "path", "size", "date"], "col_widths": {},
        "bookmarks": [], "scope": "", "geometry": "",
        "home": dict(DEFAULT_HOME),
    }


def _same_type(v, dv):
    if isinstance(dv, bool):
        return isinstance(v, bool)
    if isinstance(dv, (int, float)):
        return isinstance(v, (int, float)) and not isinstance(v, bool)
    return isinstance(v, type(dv))


def load_config(folder):
    cfg = default_config()
    try:
        with open(os.path.join(folder, "config.json"), "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return cfg
    if not isinstance(data, dict):
        return cfg
    for key, dv in list(cfg.items()):
        if key not in data:
            continue
        v = data[key]
        if key == "home":
            if isinstance(v, dict):
                for hk, hv in DEFAULT_HOME.items():
                    if hk in v and _same_type(v[hk], hv):
                        cfg["home"][hk] = v[hk]
        elif key in ("roots", "excludes", "ignored_volumes", "exclude_patterns",
                     "history", "columns"):
            if isinstance(v, list):
                cfg[key] = [str(x) for x in v]
        elif key == "bookmarks":
            if isinstance(v, list):
                cfg[key] = [b for b in v if isinstance(b, dict) and isinstance(b.get("name"), str)]
        elif key == "col_widths":
            if isinstance(v, dict):
                cfg[key] = {str(k): w for k, w in v.items()
                            if isinstance(w, int) and not isinstance(w, bool)}
        elif _same_type(v, dv):
            cfg[key] = v
    cols = set(c for c in cfg["columns"] if c in COLUMNS) | {"name"}
    cfg["columns"] = [c for c in COLUMN_ORDER if c in cols]
    cfg["result_limit"] = min(max(int(cfg["result_limit"]), 100), 50000)
    cfg["font_size"] = min(max(int(cfg["font_size"]), 8), 28)
    return cfg


def save_config(folder, cfg):
    try:
        with open(os.path.join(folder, "config.json"), "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
    except OSError:
        pass


def open_path(path):
    if sys.platform == "darwin":
        subprocess.Popen(["open", path])
    elif sys.platform == "win32":
        os.startfile(path)  # noqa
    else:
        subprocess.Popen(["xdg-open", path])


def open_privacy_settings():
    """Sistem Ayarları > Gizlilik ve Güvenlik > Tam Disk Erişimi"""
    if sys.platform == "darwin":
        subprocess.Popen(["open", "x-apple.systempreferences:"
                          "com.apple.preference.security?Privacy_AllFiles"])


def reveal_path(path):
    if sys.platform == "darwin":
        subprocess.Popen(["open", "-R", path])
    else:
        open_path(os.path.dirname(path))


def path_under(path, base):
    """path, base klasörünün altında (veya kendisi) mi? Kök "/" harici diskleri kapsamaz."""
    if base == os.sep:
        v = VOLUMES_DIR.rstrip(os.sep)
        return not (path == v or path.startswith(v + os.sep))
    return path == base or path.startswith(base.rstrip(os.sep) + os.sep)


def volume_mount_of(path):
    """/Volumes/<disk>/... -> /Volumes/<disk>; harici disk yolu değilse None."""
    prefix = VOLUMES_DIR.rstrip(os.sep) + os.sep
    if path.startswith(prefix):
        first = path[len(prefix):].split(os.sep)[0]
        if first:
            return prefix + first
    return None


def mount_online(path):
    """Yol harici bir diskteyse o disk takılı mı? (diğer yollar için her zaman True)"""
    mount = volume_mount_of(path)
    return True if mount is None else bool(_ismount(mount))


def root_online(root):
    return mount_online(root) and os.path.isdir(root)


def _boot_devs():
    devs = set()
    for p in ("/", os.path.expanduser("~")):
        try:
            devs.add(os.stat(p).st_dev)
        except OSError:
            pass
    return devs


def list_external_volumes():
    """/Volumes altındaki, sistem diski olmayan takılı diskler."""
    try:
        names = sorted(os.listdir(VOLUMES_DIR))
    except OSError:
        return []
    boot = _boot_devs()
    out = []
    for n in names:
        p = os.path.join(VOLUMES_DIR, n)
        try:
            if _ismount(p) and os.stat(p).st_dev not in boot:
                out.append(p)
        except OSError:
            pass
    return out


def _mount_types():
    """{bağlama noktası: dosya sistemi} (mount çıktısından)"""
    out = {}
    try:
        res = subprocess.run(["mount"], capture_output=True, text=True, timeout=3)
        for line in res.stdout.splitlines():
            m = re.match(r"^.+? on (.+) \((\w+)[,)]", line)
            if m:
                out[m.group(1)] = m.group(2)
    except Exception:
        pass
    return out


def list_disks():
    """Seçilebilir diskler: sistem diski + takılı harici diskler.
    [{name, path, fs, total, free, boot}]"""
    types = _mount_types()
    boot_name = "Macintosh HD"
    try:
        for n in sorted(os.listdir(VOLUMES_DIR)):
            p = os.path.join(VOLUMES_DIR, n)
            if os.path.islink(p) and os.path.realpath(p) == os.path.realpath(os.sep):
                boot_name = n
                break
    except OSError:
        pass

    def usage(p):
        try:
            u = shutil.disk_usage(p)
            return u.total, u.free
        except OSError:
            return 0, 0

    disks = []
    t, f = usage(os.sep)
    disks.append({"name": boot_name, "path": os.sep, "fs": types.get(os.sep, ""),
                  "total": t, "free": f, "boot": True})
    for p in list_external_volumes():
        t, f = usage(p)
        disks.append({"name": os.path.basename(p), "path": p, "fs": types.get(p, ""),
                      "total": t, "free": f, "boot": False})
    return disks


# --------------------------------------------------------------------------
# Veritabanı
# --------------------------------------------------------------------------

SCHEMA = """
CREATE TABLE IF NOT EXISTS dirs(
    id     INTEGER PRIMARY KEY,
    path   TEXT NOT NULL UNIQUE,
    lpath  TEXT NOT NULL,
    mtime  REAL
);
CREATE TABLE IF NOT EXISTS files(
    id     INTEGER PRIMARY KEY,
    dir_id INTEGER NOT NULL,
    name   TEXT NOT NULL,
    lname  TEXT NOT NULL,
    is_dir INTEGER NOT NULL,
    size   INTEGER NOT NULL,
    mtime  REAL NOT NULL,
    ext    TEXT NOT NULL DEFAULT '',
    btime  REAL NOT NULL DEFAULT 0
);
CREATE INDEX IF NOT EXISTS files_dir ON files(dir_id);
CREATE INDEX IF NOT EXISTS files_lname ON files(lname);
"""


@lru_cache(maxsize=64)
def _compile(pattern, flags):
    return re.compile(pattern, flags)


def _rx(pattern, ignore_case, value):
    try:
        flags = re.IGNORECASE if ignore_case else 0
        return 1 if _compile(pattern, flags).search(value or "") else 0
    except re.error:
        return 0


def _wword(target, term):
    try:
        return 1 if re.search(r"(?<!\w)" + re.escape(term) + r"(?!\w)", target or "") else 0
    except re.error:
        return 0


def _dcontains(name, term_keep):
    return 1 if term_keep in fold_keep(name or "") else 0


def _dglob(name, pattern_keep):
    return 1 if fnmatch.fnmatchcase(fold_keep(name or ""), pattern_keep) else 0


def open_db(path):
    conn = sqlite3.connect(path, check_same_thread=False, isolation_level=None, timeout=30)
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=OFF")
    version = conn.execute("PRAGMA user_version").fetchone()[0]
    if version != SCHEMA_VERSION:
        conn.execute("DROP TABLE IF EXISTS files")
        conn.execute("DROP TABLE IF EXISTS dirs")
        conn.executescript(SCHEMA)
        conn.execute(f"PRAGMA user_version={SCHEMA_VERSION}")
    else:
        conn.executescript(SCHEMA)
    conn.create_function("rx", 3, _rx, deterministic=True)
    conn.create_function("wword", 2, _wword, deterministic=True)
    conn.create_function("dcontains", 2, _dcontains, deterministic=True)
    conn.create_function("dglob", 2, _dglob, deterministic=True)
    return conn


# --------------------------------------------------------------------------
# İndeksleyici
# --------------------------------------------------------------------------

class Indexer(threading.Thread):
    """Klasörleri tarar, SQLite'a yazar ve değişiklikleri izler."""

    def __init__(self, db_path, data_folder, roots, excludes, skip_packages=True,
                 exclude_patterns=(), exclude_hidden=False):
        super().__init__(daemon=True)
        self.skip_packages = skip_packages
        self.exclude_patterns = [p for p in exclude_patterns if p]
        self.exclude_hidden = exclude_hidden
        self.force_next = False
        self.denied = set()
        self.conn = open_db(db_path)
        self.data_folder = os.path.abspath(data_folder)
        self.stop_evt = threading.Event()
        self.wake = threading.Event()
        self.lock = threading.Lock()
        self.dirty = set()
        self.full_rescan = False
        self.reconfigure = True
        self.version = 0
        self.count = 0
        self.scanned = 0
        self.scanning = True
        self.watch_mode = f"periyodik ({POLL_SECONDS} sn)"
        self.observer = None
        self.roots = []
        self.excludes = []
        self._set_paths(roots, excludes)

    # ---- yapılandırma ----------------------------------------------------
    def _set_paths(self, roots, excludes):
        norm = sorted({os.path.abspath(os.path.expanduser(r)) for r in roots if r}, key=len)
        kept = []
        for r in norm:                      # başka bir kökün içindeki kökleri ayrıca tarama
            if not any(path_under(r, k) for k in kept):
                kept.append(r)
        self.roots = kept
        self.excludes = [os.path.abspath(os.path.expanduser(e)) for e in excludes if e]
        self.excludes.append(self.data_folder)
        self.excludes.extend(SKIP_PATHS)

    def set_config(self, roots, excludes, skip_packages=None, exclude_patterns=None,
                   exclude_hidden=None):
        with self.lock:
            self._set_paths(roots, excludes)
            changed = False
            if skip_packages is not None and skip_packages != self.skip_packages:
                self.skip_packages, changed = skip_packages, True
            if exclude_patterns is not None and list(exclude_patterns) != self.exclude_patterns:
                self.exclude_patterns, changed = [p for p in exclude_patterns if p], True
            if exclude_hidden is not None and exclude_hidden != self.exclude_hidden:
                self.exclude_hidden, changed = exclude_hidden, True
            if changed:
                self.force_next = True           # ayar değişti: her şeyi yeniden listele
            self.reconfigure = True
        self.wake.set()

    def rescan_full(self):
        with self.lock:
            self.full_rescan = True
        self.wake.set()

    def stop(self):
        self.stop_evt.set()
        self.wake.set()
        self._stop_watcher()

    # ---- durum -----------------------------------------------------------
    @property
    def status(self):
        if self.scanning:
            return f"İndeksleniyor… {fmt_int(self.scanned)} klasör tarandı"
        off = sum(1 for r in self.roots if not root_online(r))
        extra = f" · {off} konum çevrimdışı" if off else ""
        if self.denied:
            extra += f" · ⚠ {fmt_int(len(self.denied))} klasöre erişilemedi"
        return f"Hazır · {fmt_int(self.count)} öğe · izleme: {self.watch_mode}{extra}"

    def _excluded(self, path):
        for e in self.excludes:
            if path == e or path.startswith(e.rstrip(os.sep) + os.sep):
                return True
        return False

    def _excluded_name(self, name):
        if self.exclude_hidden and name.startswith("."):
            return True
        low = name.lower()
        for pat in self.exclude_patterns:
            if fnmatch.fnmatchcase(low, pat.lower()):
                return True
        return False

    def _under_roots(self, path):
        return any(path_under(path, r) for r in self.roots)

    # ---- veri işlemleri --------------------------------------------------
    def _list_dir(self, d):
        """[(name, lname, is_dir, size, mtime, ext, btime)] ya da okunamazsa None."""
        out = []
        try:
            with os.scandir(d) as it:
                for e in it:
                    name = e.name
                    if (name in SKIP_NAMES or self._excluded_name(name)
                            or e.path == VOLUMES_DIR or self._excluded(e.path)):
                        continue
                    try:
                        is_dir = e.is_dir(follow_symlinks=False)
                        pkg = False
                        if is_dir and self.skip_packages and name.lower().endswith(PACKAGE_EXTS):
                            is_dir, pkg = False, True        # tek dosya gibi davran, içine girme
                        st = e.stat(follow_symlinks=False)
                        ext = "" if is_dir else os.path.splitext(name)[1].lstrip(".").lower()
                        btime = getattr(st, "st_birthtime", st.st_ctime)
                        out.append((name, fold(name), 1 if is_dir else 0,
                                    0 if (is_dir or pkg) else st.st_size, st.st_mtime,
                                    ext, btime))
                    except OSError:
                        out.append((name, fold(name), 0, 0, 0.0, "", 0.0))
        except PermissionError:
            if len(self.denied) < 5000:
                self.denied.add(d)
            return None
        except OSError:
            return None
        out.sort(key=lambda t: t[1])
        return out

    def _remove_subtree(self, d):
        base = d.rstrip(os.sep)
        lo, hi = base + os.sep, base + chr(ord(os.sep) + 1)
        cond = "path = ? OR (path >= ? AND path < ?)"
        self.conn.execute(f"DELETE FROM files WHERE dir_id IN (SELECT id FROM dirs WHERE {cond})",
                          (d, lo, hi))
        self.conn.execute(f"DELETE FROM dirs WHERE {cond}", (d, lo, hi))

    def _remove_entry(self, d):
        """Klasörü ve üst klasörün listesindeki satırını da siler."""
        self._remove_subtree(d)
        parent, name = os.path.split(d.rstrip(os.sep))
        if parent and name:
            self.conn.execute(
                "DELETE FROM files WHERE name=? AND is_dir=1 AND "
                "dir_id=(SELECT id FROM dirs WHERE path=?)", (name, parent))

    def _prune(self):
        """Artık kök klasörlerin altında olmayan ya da hariç tutulan kayıtları sil."""
        conds, params = [], []
        for r in self.roots:
            if r == os.sep:                  # sistem diski: /Volumes altı hariç her şey
                v = VOLUMES_DIR.rstrip(os.sep)
                conds.append("(NOT (path = ? OR (path >= ? AND path < ?)))")
                params += [v, v + os.sep, v + chr(ord(os.sep) + 1)]
            else:
                base = r.rstrip(os.sep)
                conds.append("(path = ? OR (path >= ? AND path < ?))")
                params += [r, base + os.sep, base + chr(ord(os.sep) + 1)]
        inside = " OR ".join(conds) if conds else "0"
        self.conn.execute("BEGIN")
        self.conn.execute(
            f"DELETE FROM files WHERE dir_id IN (SELECT id FROM dirs WHERE NOT ({inside}))", params)
        self.conn.execute(f"DELETE FROM dirs WHERE NOT ({inside})", params)
        for e in self.excludes:
            self._remove_entry(e)
        self.conn.execute("COMMIT")

    def index_tree(self, start, force_first=False, force_all=False):
        """start'tan itibaren ağacı tarar. Değişmeyen klasörler (mtime aynı) atlanır."""
        stack = [(start, force_first or force_all)]
        pending = 0
        self.conn.execute("BEGIN")
        try:
            while stack and not self.stop_evt.is_set():
                d, force = stack.pop()
                if self._excluded(d):
                    continue
                try:
                    st = os.stat(d)
                except OSError:
                    if mount_online(d):      # disk çıkarıldıysa kayıtlar saklanır
                        self._remove_entry(d)
                    continue
                row = self.conn.execute("SELECT id, mtime FROM dirs WHERE path=?", (d,)).fetchone()
                self.scanned += 1
                if row and not force and row[1] == st.st_mtime:
                    for (n,) in self.conn.execute(
                            "SELECT name FROM files WHERE dir_id=? AND is_dir=1", (row[0],)):
                        stack.append((os.path.join(d, n), False))
                    continue
                entries = self._list_dir(d)
                if entries is None:          # izin yok vb. -> sonraki turda yeniden dene
                    continue
                if row:
                    dir_id = row[0]
                else:
                    dir_id = self.conn.execute(
                        "INSERT INTO dirs(path, lpath, mtime) VALUES(?,?,?)",
                        (d, fold(d), st.st_mtime)).lastrowid
                new_sub = [e[0] for e in entries if e[2]]
                old_sub = {n for (n,) in self.conn.execute(
                    "SELECT name FROM files WHERE dir_id=? AND is_dir=1", (dir_id,))}
                for gone in old_sub - set(new_sub):
                    self._remove_subtree(os.path.join(d, gone))
                self.conn.execute("DELETE FROM files WHERE dir_id=?", (dir_id,))
                self.conn.executemany(
                    "INSERT INTO files(dir_id, name, lname, is_dir, size, mtime, ext, btime) "
                    "VALUES(?,?,?,?,?,?,?,?)",
                    [(dir_id,) + e for e in entries])
                self.conn.execute("UPDATE dirs SET mtime=? WHERE id=?", (st.st_mtime, dir_id))
                for n in new_sub:
                    stack.append((os.path.join(d, n), force_all))
                pending += len(entries)
                if pending >= BATCH_ROWS:
                    self.conn.execute("COMMIT")
                    self.conn.execute("BEGIN")
                    pending = 0
                    self.version += 1
        finally:
            self.conn.execute("COMMIT")
            self.version += 1

    def _refresh_count(self):
        self.count = self.conn.execute("SELECT count(*) FROM files").fetchone()[0]
        self.version += 1

    def full_pass(self, force=False):
        self.scanning = True
        self.scanned = 0
        self.denied = set()
        try:
            self._prune()
            for r in list(self.roots):
                if self.stop_evt.is_set():
                    break
                if root_online(r):
                    self.index_tree(r, force_all=force)
        finally:
            self._refresh_count()
            self.scanning = False

    # ---- izleme ----------------------------------------------------------
    def mark_dirty(self, paths):
        added = False
        for p in paths:
            if not p:
                continue
            d = os.path.dirname(os.fsdecode(p))
            if self._excluded(d) or not self._under_roots(d):
                continue
            with self.lock:
                self.dirty.add(d)
            added = True
        if added:
            self.wake.set()

    def _stop_watcher(self):
        obs, self.observer = self.observer, None
        if obs is not None:
            try:
                obs.stop()
            except Exception:
                pass

    def _start_watcher(self):
        self._stop_watcher()
        try:
            from watchdog.observers import Observer
            from watchdog.events import FileSystemEventHandler
        except Exception:
            self.watch_mode = f"periyodik ({POLL_SECONDS} sn)"
            return
        indexer = self

        class Handler(FileSystemEventHandler):
            def on_any_event(self, event):
                if event.event_type in ("opened", "closed", "closed_no_write"):
                    return
                paths = [event.src_path]
                dest = getattr(event, "dest_path", "")
                if dest:
                    paths.append(dest)
                indexer.mark_dirty(paths)

        try:
            obs = Observer()
            for r in self.roots:
                if root_online(r):
                    obs.schedule(Handler(), r, recursive=True)
            obs.daemon = True
            obs.start()
            self.observer = obs
            self.watch_mode = "gerçek zamanlı"
        except Exception:
            self.observer = None
            self.watch_mode = f"periyodik ({POLL_SECONDS} sn)"

    # ---- ana döngü -------------------------------------------------------
    def run(self):
        try:
            self._refresh_count()
            last_poll = time.time()
            while not self.stop_evt.is_set():
                with self.lock:
                    reconf, self.reconfigure = self.reconfigure, False
                    full, self.full_rescan = self.full_rescan, False
                    force_pk, self.force_next = self.force_next, False
                    dirty, self.dirty = self.dirty, set()
                if reconf or full:
                    self.full_pass(force=full or force_pk)
                    if reconf:
                        self._start_watcher()
                    last_poll = time.time()
                elif dirty:
                    self.scanning = True
                    self.scanned = 0
                    try:
                        for d in sorted(dirty):
                            if self.stop_evt.is_set():
                                break
                            if (self._under_roots(d) and not self._excluded(d)
                                    and mount_online(d)):
                                self.index_tree(d, force_first=True)
                    finally:
                        self._refresh_count()
                        self.scanning = False
                elif self.observer is None and time.time() - last_poll > POLL_SECONDS:
                    self.full_pass(force=False)
                    last_poll = time.time()
                self.wake.wait(timeout=1.0)
                if self.wake.is_set() and not self.stop_evt.is_set():
                    time.sleep(0.4)          # art arda gelen olayları birleştir
                    self.wake.clear()
        finally:
            self._stop_watcher()


# --------------------------------------------------------------------------
# Arama sorgusu
# --------------------------------------------------------------------------

class QueryError(Exception):
    pass


Req = namedtuple("Req", "gen text match_case match_path regex sort_col sort_desc refresh "
                 "filter_name whole_word diacritics scope",
                 defaults=("Hepsi", False, False, ""))
QOpts = namedtuple("QOpts", "match_case match_path whole_word diacritics")

FILTERS = {
    "Hepsi": None,
    "Ses": ("ext", "aac aif aiff alac ape flac m4a mp3 ogg opus wav wma"),
    "Sıkıştırılmış": ("ext", "7z bz2 dmg gz iso rar tar tgz xz zip"),
    "Belge": ("ext", "csv doc docx epub key md numbers odt pages pdf ppt pptx rtf txt xls xlsx"),
    "Uygulama": ("app", "pkg command sh"),
    "Klasör": ("dir", ""),
    "Resim": ("ext", "ai arw bmp cr2 gif heic jpeg jpg nef png psd raw svg tif tiff webp"),
    "Video": ("ext", "avi flv m4v mkv mov mp4 mpeg mpg webm wmv"),
}


def filter_cond(name):
    spec = FILTERS.get(name)
    if not spec:
        return None, []
    kind, exts = spec
    if kind == "dir":
        return "f.is_dir = 1", []
    patterns = ["*." + e for e in exts.split()]
    file_cond = "f.is_dir = 0 AND (" + " OR ".join("f.lname GLOB ?" for _ in patterns) + ")"
    if kind == "app":                      # .app paketleri macOS'ta klasördür
        return f"(f.lname GLOB ? OR ({file_cond}))", ["*.app"] + patterns
    return file_cond, patterns


def _add_months(d, n):
    y, m = divmod(d.month - 1 + n, 12)
    return d.replace(year=d.year + y, month=m + 1, day=1)


def _period(lit):
    """today / 2024 / 2024-05 / 2024-05-17 / 17.05.2024 -> (başlangıç_ts, bitiş_ts)"""
    lit = lit.strip().lower()
    today = datetime.now().replace(hour=0, minute=0, second=0, microsecond=0)
    day = timedelta(days=1)
    if lit == "today":
        s, e = today, today + day
    elif lit == "yesterday":
        s, e = today - day, today
    elif lit in ("thisweek", "lastweek"):
        s = today - timedelta(days=today.weekday())
        if lit == "lastweek":
            s -= timedelta(days=7)
        e = s + timedelta(days=7)
    elif lit in ("thismonth", "lastmonth"):
        s = _add_months(today.replace(day=1), 0 if lit == "thismonth" else -1)
        e = _add_months(s, 1)
    elif lit in ("thisyear", "lastyear"):
        y = today.year - (1 if lit == "lastyear" else 0)
        s, e = datetime(y, 1, 1), datetime(y + 1, 1, 1)
    else:
        m = re.match(r"^(\d{4})(?:-(\d{1,2})(?:-(\d{1,2}))?)?$", lit)
        if m:
            y = int(m.group(1))
            if m.group(3):
                s = datetime(y, int(m.group(2)), int(m.group(3)))
                e = s + day
            elif m.group(2):
                s = datetime(y, int(m.group(2)), 1)
                e = _add_months(s, 1)
            else:
                s, e = datetime(y, 1, 1), datetime(y + 1, 1, 1)
        else:
            m = re.match(r"^(\d{1,2})\.(\d{1,2})\.(\d{4})$", lit)
            if not m:
                raise ValueError(lit)
            s = datetime(int(m.group(3)), int(m.group(2)), int(m.group(1)))
            e = s + day
    return s.timestamp(), e.timestamp()


def _dm_cond(spec):
    m = re.match(r"^(>=|<=|>|<|=)?(.*)$", spec.strip())
    op, val = m.group(1) or "=", m.group(2).strip()
    try:
        if ".." in val:
            a, b = val.split("..", 1)
            return "f.mtime >= ? AND f.mtime < ?", [_period(a)[0], _period(b)[1]]
        start, end = _period(val)
    except ValueError:
        raise QueryError("dm: örnekler -> dm:today  dm:2024  dm:>2024-05-01  dm:2023..2024")
    if op == "=":
        return "f.mtime >= ? AND f.mtime < ?", [start, end]
    if op == ">":
        return "f.mtime >= ?", [end]
    if op == ">=":
        return "f.mtime >= ?", [start]
    if op == "<":
        return "f.mtime < ?", [start]
    return "f.mtime < ?", [end]                        # <=
Compiled = namedtuple("Compiled", "select count params")

SIZE_RE = re.compile(r"^(>=|<=|>|<|=)?\s*([0-9]+(?:[.,][0-9]+)?)\s*([a-zA-Z]*)$")
UNITS = {"": 1, "b": 1, "k": 1024, "kb": 1024, "m": 1024 ** 2, "mb": 1024 ** 2,
         "g": 1024 ** 3, "gb": 1024 ** 3, "t": 1024 ** 4, "tb": 1024 ** 4}
SORTS = {"name": "f.lname {d}", "path": "d.lpath {d}, f.lname {d}",
         "size": "f.size {d}, f.lname", "date": "f.mtime {d}, f.lname",
         "ext": "f.ext {d}, f.lname", "type": "f.is_dir {d}, f.ext {d}, f.lname",
         "btime": "f.btime {d}, f.lname"}


def _term_cond(term, o, force_path=False):
    use_path = o.match_path or force_path or "/" in term
    if o.match_case:
        t = unicodedata.normalize("NFC", term)
        target = "(d.path || '/' || f.name)" if use_path else "f.name"
        raw = None
    else:
        t = fold(term)
        target = "(d.lpath || '/' || f.lname)" if use_path else "f.lname"
        raw = "(d.path || '/' || f.name)" if use_path else "f.name"
    if "*" in t or "?" in t:
        sql, params = f"{target} GLOB ?", [t.replace("[", "[[]")]
        if o.diacritics and raw:
            sql = f"({sql} AND dglob({raw}, ?) = 1)"
            params.append(fold_keep(term))
    else:
        sql, params = f"instr({target}, ?) > 0", [t]
        if o.whole_word:
            sql = f"({sql} AND wword({target}, ?) = 1)"
            params.append(t)
        if o.diacritics and raw:
            sql = f"({sql} AND dcontains({raw}, ?) = 1)"
            params.append(fold_keep(term))
    return sql, params, use_path


def build_where(text, match_case=False, match_path=False, regex=False,
                whole_word=False, diacritics=False):
    """Arama metnini SQL WHERE parçasına çevirir -> (where, params, needs_dirs)."""
    opts = QOpts(match_case, match_path, whole_word, diacritics)
    text = text.strip()
    if not text:
        return "1", [], False

    if regex or text.lower().startswith("regex:"):
        pattern = text[6:].strip() if text.lower().startswith("regex:") else text
        try:
            re.compile(pattern)
        except re.error as e:
            raise QueryError(f"Geçersiz düzenli ifade: {e}")
        ic = 0 if match_case else 1
        if match_path:
            return "rx(?, ?, d.path || '/' || f.name)", [pattern, ic], True
        return "rx(?, ?, f.name)", [pattern, ic], False

    conds, params, needs_dirs = [], [], False
    for m in re.finditer(r'"([^"]*)"|(\S+)', text):
        quoted = m.group(1) is not None
        tok = m.group(1) if quoted else m.group(2)
        if not tok:
            continue
        neg = False
        if not quoted and tok.startswith("!") and len(tok) > 1:
            neg, tok = True, tok[1:]
        low = tok.lower()
        c, p = None, []
        force_path = False

        if not quoted and low in ("folder:", "folders:"):
            c = "f.is_dir = 1"
        elif not quoted and low in ("file:", "files:"):
            c = "f.is_dir = 0"
        elif not quoted and low.startswith("ext:"):
            exts = [re.sub(r"[*?\[\]]", "", fold(e.strip().lstrip(".")))
                    for e in re.split(r"[;,]", tok[4:]) if e.strip()]
            exts = [e for e in exts if e]
            if not exts:
                continue
            c = "f.is_dir = 0 AND (" + " OR ".join("f.lname GLOB ?" for _ in exts) + ")"
            p = ["*." + e for e in exts]
        elif not quoted and low.startswith("size:"):
            sm = SIZE_RE.match(tok[5:].strip())
            if not sm or sm.group(3).lower() not in UNITS:
                raise QueryError("size: örnek kullanım -> size:>10mb")
            op = sm.group(1) or "="
            value = float(sm.group(2).replace(",", ".")) * UNITS[sm.group(3).lower()]
            c = f"f.is_dir = 0 AND f.size {op} ?"
            p = [int(value)]
        elif not quoted and low.startswith("dm:"):
            c, p = _dm_cond(tok[3:])
        else:
            if not quoted and low.startswith("path:") and len(tok) > 5:
                tok, force_path = tok[5:], True
            alts = tok.split("|") if (not quoted and "|" in tok) else [tok]
            parts = []
            for a in alts:
                if not a:
                    continue
                sql, sp, nd = _term_cond(a, opts, force_path)
                parts.append(sql)
                p += sp
                needs_dirs = needs_dirs or nd
            if not parts:
                continue
            c = " OR ".join(parts)

        conds.append(f"NOT ({c})" if neg else f"({c})")
        params += p

    return (" AND ".join(conds) if conds else "1"), params, needs_dirs


def scope_cond(path):
    """Aramayı bir disk/klasörle sınırla. Sistem diski "/" harici diskleri kapsamaz."""
    if path == os.sep:
        v = VOLUMES_DIR.rstrip(os.sep)
        return ("NOT (d.path = ? OR (d.path >= ? AND d.path < ?))",
                [v, v + os.sep, v + chr(ord(os.sep) + 1)])
    base = path.rstrip(os.sep)
    return ("(d.path = ? OR (d.path >= ? AND d.path < ?))",
            [path, base + os.sep, base + chr(ord(os.sep) + 1)])


def compile_query(req):
    where, params, needs_dirs = build_where(req.text, req.match_case, req.match_path, req.regex,
                                            req.whole_word, req.diacritics)
    order = ""
    if req.sort_col in SORTS:
        order = " ORDER BY " + SORTS[req.sort_col].format(d="DESC" if req.sort_desc else "ASC")
    fc, fp = filter_cond(req.filter_name)
    if fc:
        where = f"({where}) AND ({fc})"
        params = params + fp
    if req.scope:
        sc, sp = scope_cond(req.scope)
        where = f"({where}) AND ({sc})"
        params = params + sp
        needs_dirs = True
    select = ("SELECT f.name, d.path, f.is_dir, f.size, f.mtime, f.ext, f.btime "
              "FROM files f CROSS JOIN dirs d ON d.id = f.dir_id "
              f"WHERE {where}{order} LIMIT {RESULT_LIMIT}")
    if needs_dirs:
        count = f"SELECT count(*) FROM files f CROSS JOIN dirs d ON d.id = f.dir_id WHERE {where}"
    else:
        count = f"SELECT count(*) FROM files f WHERE {where}"
    return Compiled(select, count, params)


class Searcher(threading.Thread):
    """Aramaları arka planda yürütür; yeni sorgu gelince eskisini yarıda keser."""

    def __init__(self, db_path, out):
        super().__init__(daemon=True)
        self.db_path = db_path
        self.out = out
        self.cv = threading.Condition()
        self.req = None
        self.conn = None
        self.busy = False
        self.alive = True

    def submit(self, req):
        with self.cv:
            self.req = req
            self.cv.notify()
        if self.busy and self.conn is not None:
            try:
                self.conn.interrupt()
            except sqlite3.Error:
                pass

    def stop(self):
        with self.cv:
            self.alive = False
            self.cv.notify()

    def _execute(self, req):
        try:
            q = compile_query(req)
        except QueryError as e:
            self.out.put((req, None, None, str(e)))
            return
        rows = self.conn.execute(q.select, q.params).fetchall()
        if len(rows) < RESULT_LIMIT:
            self.out.put((req, rows, len(rows), None))
            return
        self.out.put((req, rows, None, None))          # önce satırlar
        total = self.conn.execute(q.count, q.params).fetchone()[0]
        self.out.put((req, None, total, None))         # sonra toplam sayı

    def run(self):
        self.conn = open_db(self.db_path)
        while True:
            with self.cv:
                while self.req is None and self.alive:
                    self.cv.wait()
                if not self.alive:
                    return
                req, self.req = self.req, None
            self.busy = True
            try:
                self._execute(req)
            except sqlite3.OperationalError as e:
                if "interrupt" in str(e).lower():
                    with self.cv:
                        if self.req is None:      # eski bir kesinti: tekrar dene
                            self.req = req
                else:
                    self.out.put((req, None, None, f"Veritabanı hatası: {e}"))
            except sqlite3.Error as e:
                self.out.put((req, None, None, f"Veritabanı hatası: {e}"))
            finally:
                self.busy = False



# --------------------------------------------------------------------------
# Arayüz
# --------------------------------------------------------------------------

TYPE_NAMES = {"app": "Uygulama", "pkg": "Kurulum paketi", "dmg": "Disk görüntüsü",
              "photoslibrary": "Fotoğraflar kitaplığı"}


def type_text(ext, is_dir):
    if is_dir:
        return "Klasör"
    if not ext:
        return "Dosya"
    return TYPE_NAMES.get(ext, ext.upper() + " dosyası")


def applescript_escape(s):
    return s.replace("\\", "\\\\").replace('"', '\\"')


SYNTAX_HELP = """\
ARAMA SÖZDİZİMİ

  rapor 2024           iki kelime de adda geçsin (AND)
  "bütçe planı"        tırnak içindeki ifade tek parça aranır
  foo|bar              foo VEYA bar
  !taslak              "taslak" geçmesin
  *.pdf    a?c*        joker karakterler (adın tamamıyla eşleşir)

FİLTRELER

  ext:mp4;mov          uzantıya göre
  size:>100mb          boyuta göre (>, <, >=, <=, =  ve kb mb gb tb)
  folder:   file:      yalnızca klasörler / yalnızca dosyalar
  dm:today             değiştirilme tarihi
                       today, yesterday, thisweek, lastweek, thismonth, lastmonth,
                       thisyear, lastyear, 2024, 2024-05, 2024-05-17, 17.05.2024,
                       dm:>2024-01-01, dm:<2023, dm:2023..2024
  path:belgeler        yolda ara
  Belgeler/rapor       içinde "/" olan terimler yolda aranır
  regex:^IMG_\\d+      düzenli ifade (veya Ara > Düzenli İfade)

ARA MENÜSÜ SEÇENEKLERİ

  Büyük/Küçük Harf Duyarlı   Rapor ile rapor farklı sayılır
  Tam Kelime                 yalnızca bütün kelime eşleşir
  Yolu Eşleştir              klasör yolunda da ara
  Aksanları Eşleştir         ş, ğ, ç, ö, ü, ı harfleri ayrı sayılır
                             (kapalıyken "sarki" yazınca "şarkı" da bulunur)

Sağ üstteki Konum kutusu aramayı tek bir diske veya klasöre sınırlar,
Filtre kutusu ise dosya türüne göre süzer.
"""


class App:
    def __init__(self):
        self.folder = data_dir()
        self.db_path = os.path.join(self.folder, "index.db")
        self.cfg = load_config(self.folder)
        set_result_limit(self.cfg["result_limit"])

        self.indexer = Indexer(self.db_path, self.folder, self.cfg["roots"], self.cfg["excludes"],
                               self.cfg["skip_packages"], self.cfg["exclude_patterns"],
                               self.cfg["exclude_hidden"])
        self.out = queue.Queue()
        self.searcher = Searcher(self.db_path, self.out)

        home = self.cfg["home"]
        self.sort_col = home["sort"] if home["sort"] in COLUMNS else "name"
        self.sort_desc = home["desc"]
        self.gen = 0
        self.rows = []
        self.total = None
        self.seen_version = -1
        self.last_refresh = 0.0
        self._vol_check = 0.0
        self._vol_state = None
        self.search_job = None
        self.history_job = None
        self.scope_map = {"Her yerde": ""}
        self.scope_first = True
        self.opts_dialog = None

        self._build_ui()
        self.refresh_scopes()
        self.searcher.start()
        self.indexer.start()
        self.run_search()
        self.root.after(100, self.poll)

    # ======================================================================
    # Pencere
    # ======================================================================
    def _build_ui(self):
        cfg, home = self.cfg, self.cfg["home"]
        self.root = root = tk.Tk()
        root.title(f"Everything {APP_VERSION}")
        root.geometry(cfg["geometry"] or "1100x650")
        root.minsize(720, 420)
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        try:   # eski Tk (8.5 / <8.6.10) emoji çizerken sorun çıkarabilir
            ver = tuple(int(x) for x in str(root.tk.call("info", "patchlevel")).split(".")[:3])
            self.use_emoji = ver >= (8, 6, 10)
        except Exception:
            self.use_emoji = False

        self.query = tk.StringVar(value=home["search"])
        self.var_case = tk.BooleanVar(value=home["match_case"])
        self.var_path = tk.BooleanVar(value=home["match_path"])
        self.var_regex = tk.BooleanVar(value=home["regex"])
        self.var_word = tk.BooleanVar(value=home["whole_word"])
        self.var_diac = tk.BooleanVar(value=home["diacritics"])
        self.var_filter = tk.StringVar(value=home["filter"] if home["filter"] in FILTERS else "Hepsi")
        self.var_scope = tk.StringVar(value="Her yerde")
        self.var_status = tk.BooleanVar(value=cfg["show_status"])
        self.var_top = tk.BooleanVar(value=cfg["always_on_top"])
        self.var_sort = tk.StringVar(value=self.sort_col)
        self.var_desc = tk.BooleanVar(value=self.sort_desc)
        self.col_vars = {c: tk.BooleanVar(value=c in cfg["columns"]) for c in COLUMN_ORDER}
        self.style = ttk.Style(root)

        self._build_searchbar()
        self._build_statusbar()
        self._build_results()
        self._build_menus()
        self._bind_keys()
        self.apply_font()
        self.apply_columns()
        self.update_headings()
        self.apply_window_flags()
        self.entry.focus_set()

    def _build_searchbar(self):
        bar = ttk.Frame(self.root, padding=(8, 8, 8, 6))
        bar.pack(side="top", fill="x")
        self.entry = ttk.Combobox(bar, textvariable=self.query, values=self.cfg["history"])
        self.entry.pack(side="left", fill="x", expand=True)
        ttk.Label(bar, text="Konum:").pack(side="left", padx=(12, 4))
        self.scope_combo = ttk.Combobox(bar, textvariable=self.var_scope, state="readonly",
                                        width=16, values=["Her yerde"])
        self.scope_combo.pack(side="left")
        ttk.Label(bar, text="Filtre:").pack(side="left", padx=(12, 4))
        self.filter_combo = ttk.Combobox(bar, textvariable=self.var_filter, state="readonly",
                                         width=13, values=list(FILTERS))
        self.filter_combo.pack(side="left")
        self.query.trace_add("write", lambda *_: self.on_query_typed())
        self.entry.bind("<<ComboboxSelected>>", lambda e: self.run_search_now())
        self.scope_combo.bind("<<ComboboxSelected>>", lambda e: self.on_scope_changed())
        self.filter_combo.bind("<<ComboboxSelected>>", lambda e: self.schedule_search())

    def _build_statusbar(self):
        self.status_frame = ttk.Frame(self.root, padding=(10, 3, 10, 6))
        self.lbl_count = ttk.Label(self.status_frame, text="")
        self.lbl_count.pack(side="left")
        self.lbl_sel = ttk.Label(self.status_frame, text="")
        self.lbl_sel.pack(side="left", padx=(24, 0))
        self.lbl_index = ttk.Label(self.status_frame, text="")
        self.lbl_index.pack(side="right")
        if self.cfg["show_status"]:
            self.status_frame.pack(side="bottom", fill="x")

    def _build_results(self):
        self.results_frame = ttk.Frame(self.root)
        self.results_frame.pack(side="top", fill="both", expand=True, padx=8, pady=(0, 2))
        self.tree = ttk.Treeview(self.results_frame, columns=COLUMN_ORDER, show="headings",
                                 selectmode="extended")
        for c in COLUMN_ORDER:
            title, width, anchor = COLUMNS[c]
            self.tree.heading(c, text=title, command=lambda col=c: self.sort_by(col))
            self.tree.column(c, width=self.cfg["col_widths"].get(c, width), anchor=anchor,
                             stretch=c in ("name", "path"))
        vsb = ttk.Scrollbar(self.results_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", lambda e: self.update_selection_label())

    # ---- menüler -----------------------------------------------------------
    def _build_menus(self):
        root = self.root
        mb = tk.Menu(root)

        m = tk.Menu(mb, tearoff=0)
        m.add_command(label="Aç", accelerator="Enter", command=self.open_selected)
        m.add_command(label="Üst Klasörü Finder'da Göster", command=self.reveal_selected)
        m.add_command(label="Özellikler (Bilgi Al)", command=self.get_info)
        m.add_separator()
        m.add_command(label="Sonuçları Dışa Aktar…", command=self.export_results)
        m.add_separator()
        m.add_command(label="Kapat", accelerator="⌘W", command=self.on_close)
        mb.add_cascade(label="Dosya", menu=m)

        m = tk.Menu(mb, tearoff=0)
        m.add_command(label="Tam Yolu ve Adı Kopyala", accelerator="⌘C",
                      command=lambda: self.copy_selected("full"))
        m.add_command(label="Klasör Yolunu Kopyala", command=lambda: self.copy_selected("dir"))
        m.add_command(label="Adı Kopyala", command=lambda: self.copy_selected("name"))
        m.add_separator()
        m.add_command(label="Tümünü Seç", accelerator="⌘A", command=self.select_all)
        m.add_command(label="Seçimi Ters Çevir", command=self.invert_selection)
        m.add_separator()
        m.add_command(label="Çöpe Taşı…", accelerator="⌘⌫", command=self.trash_selected)
        mb.add_cascade(label="Düzen", menu=m)

        m = tk.Menu(mb, tearoff=0)
        m.add_checkbutton(label="Durum Çubuğu", variable=self.var_status, command=self.toggle_status)
        m.add_checkbutton(label="Her Zaman Üstte", variable=self.var_top, command=self.toggle_top)
        m.add_separator()
        cm = tk.Menu(m, tearoff=0)
        for c in COLUMN_ORDER[1:]:
            cm.add_checkbutton(label=COLUMNS[c][0], variable=self.col_vars[c],
                               command=self.toggle_column)
        m.add_cascade(label="Sütunlar", menu=cm)
        sm = tk.Menu(m, tearoff=0)
        for c in COLUMN_ORDER:
            sm.add_radiobutton(label=COLUMNS[c][0], variable=self.var_sort, value=c,
                               command=self.sort_from_menu)
        sm.add_separator()
        sm.add_checkbutton(label="Azalan Sırada", variable=self.var_desc, command=self.sort_from_menu)
        m.add_cascade(label="Sırala", menu=sm)
        m.add_separator()
        m.add_command(label="Yazı Boyutunu Büyüt", accelerator="⌘+", command=lambda: self.zoom(1))
        m.add_command(label="Yazı Boyutunu Küçült", accelerator="⌘-", command=lambda: self.zoom(-1))
        m.add_command(label="Varsayılan Yazı Boyutu", accelerator="⌘0", command=lambda: self.zoom(0))
        m.add_separator()
        m.add_command(label="Yenile", accelerator="F5", command=self.run_search_now)
        mb.add_cascade(label="Görünüm", menu=m)

        m = tk.Menu(mb, tearoff=0)
        m.add_checkbutton(label="Büyük/Küçük Harf Duyarlı", accelerator="⌘I",
                          variable=self.var_case, command=self.schedule_search)
        m.add_checkbutton(label="Tam Kelime", accelerator="⌘B",
                          variable=self.var_word, command=self.schedule_search)
        m.add_checkbutton(label="Yolu Eşleştir", accelerator="⌘U",
                          variable=self.var_path, command=self.schedule_search)
        m.add_checkbutton(label="Aksanları Eşleştir",
                          variable=self.var_diac, command=self.schedule_search)
        m.add_checkbutton(label="Düzenli İfade", accelerator="⌘R",
                          variable=self.var_regex, command=self.schedule_search)
        m.add_separator()
        for i, name in enumerate(FILTERS, 1):
            m.add_radiobutton(label=name, variable=self.var_filter, value=name,
                              accelerator=f"⌘{i}" if i <= 8 else "", command=self.schedule_search)
        m.add_separator()
        self.scope_menu = tk.Menu(m, tearoff=0)
        m.add_cascade(label="Konum", menu=self.scope_menu)
        mb.add_cascade(label="Ara", menu=m)

        self.bookmarks_menu = tk.Menu(mb, tearoff=0)
        mb.add_cascade(label="Yer İmleri", menu=self.bookmarks_menu)
        self.rebuild_bookmarks_menu()

        m = tk.Menu(mb, tearoff=0)
        m.add_command(label="Seçenekler…", accelerator="⌘,", command=self.open_options)
        m.add_separator()
        m.add_command(label="İndeksi Baştan Tara", command=self.indexer.rescan_full)
        m.add_command(label="Tam Disk Erişimi Ayarlarını Aç…", command=open_privacy_settings)
        mb.add_cascade(label="Araçlar", menu=m)

        m = tk.Menu(mb, tearoff=0)
        m.add_command(label="Arama Sözdizimi", command=self.show_syntax)
        m.add_separator()
        m.add_command(label="Everything Hakkında", command=self.show_about)
        mb.add_cascade(label="Yardım", menu=m)
        root.config(menu=mb)

        self.row_menu = tk.Menu(root, tearoff=0)
        self.row_menu.add_command(label="Aç", command=self.open_selected)
        self.row_menu.add_command(label="Üst Klasörü Finder'da Göster", command=self.reveal_selected)
        self.row_menu.add_separator()
        self.row_menu.add_command(label="Tam Yolu ve Adı Kopyala",
                                  command=lambda: self.copy_selected("full"))
        self.row_menu.add_command(label="Klasör Yolunu Kopyala",
                                  command=lambda: self.copy_selected("dir"))
        self.row_menu.add_command(label="Adı Kopyala", command=lambda: self.copy_selected("name"))
        self.row_menu.add_separator()
        self.row_menu.add_command(label="Özellikler (Bilgi Al)", command=self.get_info)
        self.row_menu.add_command(label="Çöpe Taşı…", command=self.trash_selected)

        self.col_menu = tk.Menu(root, tearoff=0)
        for c in COLUMN_ORDER[1:]:
            self.col_menu.add_checkbutton(label=COLUMNS[c][0], variable=self.col_vars[c],
                                          command=self.toggle_column)

    def _bind(self, widget, seq, fn):
        try:
            widget.bind(seq, fn)
        except tk.TclError:          # bu platformda olmayan tuş adı
            pass

    def _bind_keys(self):
        root, tree = self.root, self.tree
        b = self._bind
        b(self.entry, "<Return>", lambda e: self.on_enter())
        b(self.entry, "<Escape>", lambda e: self.query.set(""))
        b(self.entry, "<Down>", self.focus_tree)
        b(tree, "<Return>", lambda e: self.open_selected())
        b(tree, "<Double-1>", self.on_double_click)
        b(tree, "<Command-c>", lambda e: self.copy_selected("full"))
        b(tree, "<Command-a>", lambda e: self.select_all())
        b(tree, "<Delete>", lambda e: self.trash_selected())
        b(tree, "<Command-BackSpace>", lambda e: self.trash_selected())
        for seq in ("<Button-2>", "<Button-3>", "<Control-Button-1>"):
            b(tree, seq, self.show_menu)
        b(root, "<Command-f>", self.focus_entry)
        b(root, "<Command-w>", lambda e: self.on_close())
        b(root, "<Command-comma>", lambda e: self.open_options())
        b(root, "<Command-i>", lambda e: self.flip(self.var_case))
        b(root, "<Command-b>", lambda e: self.flip(self.var_word))
        b(root, "<Command-u>", lambda e: self.flip(self.var_path))
        b(root, "<Command-r>", lambda e: self.flip(self.var_regex))
        b(root, "<Command-d>", lambda e: self.add_bookmark())
        b(root, "<F5>", lambda e: self.run_search_now())
        b(root, "<Command-equal>", lambda e: self.zoom(1))
        b(root, "<Command-plus>", lambda e: self.zoom(1))
        b(root, "<Command-minus>", lambda e: self.zoom(-1))
        b(root, "<Command-0>", lambda e: self.zoom(0))
        for i, name in enumerate(FILTERS, 1):
            if i <= 8:
                b(root, f"<Command-Key-{i}>", lambda e, n=name: self.set_filter(n))

    # ======================================================================
    # Görünüm ayarları
    # ======================================================================
    def apply_font(self):
        size = self.cfg["font_size"]
        try:
            fam = tkfont.nametofont("TkDefaultFont").actual("family")
        except Exception:
            fam = "Helvetica"
        self.style.configure("Treeview", font=(fam, size), rowheight=int(size * 1.9))
        self.style.configure("Treeview.Heading", font=(fam, size))
        self.entry.configure(font=(fam, size + 3))

    def zoom(self, delta):
        size = 13 if delta == 0 else self.cfg["font_size"] + delta
        self.cfg["font_size"] = min(max(size, 8), 28)
        self.apply_font()

    def apply_columns(self):
        cols = [c for c in COLUMN_ORDER if c in self.cfg["columns"]] or ["name"]
        self.tree.configure(displaycolumns=cols)
        for c in COLUMN_ORDER:
            self.col_vars[c].set(c in cols)

    def toggle_column(self):
        cols = [c for c in COLUMN_ORDER if c == "name" or self.col_vars[c].get()]
        self.cfg["columns"] = cols
        self.apply_columns()
        save_config(self.folder, self.cfg)

    def apply_window_flags(self):
        self.var_top.set(self.cfg["always_on_top"])
        self.var_status.set(self.cfg["show_status"])
        try:
            self.root.attributes("-topmost", bool(self.cfg["always_on_top"]))
        except tk.TclError:
            pass
        self._show_status(self.cfg["show_status"])

    def _show_status(self, show):
        if show:
            self.status_frame.pack(side="bottom", fill="x", before=self.results_frame)
        else:
            self.status_frame.pack_forget()

    def toggle_status(self):
        self.cfg["show_status"] = bool(self.var_status.get())
        self._show_status(self.cfg["show_status"])
        save_config(self.folder, self.cfg)

    def toggle_top(self):
        self.cfg["always_on_top"] = bool(self.var_top.get())
        self.apply_window_flags()
        save_config(self.folder, self.cfg)

    def flip(self, var):
        var.set(not var.get())
        self.schedule_search()
        return "break"

    def set_filter(self, name):
        self.var_filter.set(name)
        self.schedule_search()
        return "break"

    def update_headings(self):
        for c in COLUMN_ORDER:
            mark = (" ▼" if self.sort_desc else " ▲") if c == self.sort_col else ""
            self.tree.heading(c, text=COLUMNS[c][0] + mark)
        self.var_sort.set(self.sort_col)
        self.var_desc.set(self.sort_desc)

    def sort_by(self, col):
        if self.sort_col == col:
            self.sort_desc = not self.sort_desc
        else:
            self.sort_col, self.sort_desc = col, False
        self.update_headings()
        self.run_search()

    def sort_from_menu(self):
        self.sort_col = self.var_sort.get()
        self.sort_desc = bool(self.var_desc.get())
        self.update_headings()
        self.run_search()

    # ======================================================================
    # Arama
    # ======================================================================
    def scope_path(self):
        return self.scope_map.get(self.var_scope.get(), "")

    def current_req(self, refresh=False):
        return Req(self.gen, self.query.get(), self.var_case.get(), self.var_path.get(),
                   self.var_regex.get(), self.sort_col, self.sort_desc, refresh,
                   self.var_filter.get(), self.var_word.get(), self.var_diac.get(),
                   self.scope_path())

    def schedule_search(self):
        if self.search_job is not None:
            self.root.after_cancel(self.search_job)
        self.search_job = self.root.after(60, self.run_search)

    def run_search(self, refresh=False):
        self.search_job = None
        self.gen += 1
        self.searcher.submit(self.current_req(refresh))

    def run_search_now(self):
        if self.search_job is not None:
            self.root.after_cancel(self.search_job)
        self.run_search()

    def on_query_typed(self):
        if self.cfg["search_as_you_type"]:
            self.schedule_search()
        if self.history_job is not None:
            self.root.after_cancel(self.history_job)
        self.history_job = self.root.after(1500, self.commit_history)

    def on_enter(self):
        self.run_search_now()
        self.commit_history()
        self.open_selected(first_if_none=True)

    def on_scope_changed(self):
        self.cfg["scope"] = self.scope_path()
        self.schedule_search()

    def commit_history(self):
        self.history_job = None
        text = self.query.get().strip()
        if not text or not self.cfg["save_history"]:
            return
        hist = [h for h in self.cfg["history"] if h != text]
        hist.insert(0, text)
        self.cfg["history"] = hist[:50]
        self.entry.configure(values=self.cfg["history"])
        save_config(self.folder, self.cfg)

    def clear_history(self):
        self.cfg["history"] = []
        self.entry.configure(values=[])
        save_config(self.folder, self.cfg)

    # ---- konum (disk/klasör) listesi ------------------------------------------
    def refresh_scopes(self):
        items = [("Her yerde", "")]
        disks = list_disks()
        used = set()
        for d in disks:
            items.append((d["name"], d["path"]))
            used.add(d["path"])
        for r in self.cfg["roots"]:
            if r in used:
                continue
            items.append((os.path.basename(r.rstrip(os.sep)) or r, r))
            used.add(r)
        labels, scope_map = [], {}
        for label, path in items:
            if label in scope_map:
                label = f"{label} ({path})"
            scope_map[label] = path
            labels.append(label)
        self.scope_map = scope_map
        self.scope_combo.configure(values=labels)
        current = self.var_scope.get()
        if self.scope_first:
            self.scope_first = False
            saved = self.cfg.get("scope", "")
            current = next((l for l, p in scope_map.items() if p == saved), "Her yerde")
        elif current not in scope_map:
            current = "Her yerde"
        self.var_scope.set(current)
        self.scope_menu.delete(0, "end")
        for label in labels:
            self.scope_menu.add_radiobutton(label=label, variable=self.var_scope, value=label,
                                            command=self.on_scope_changed)

    # ======================================================================
    # Sonuçlar
    # ======================================================================
    def poll(self):
        try:
            while True:
                self.handle_result(*self.out.get_nowait())
        except queue.Empty:
            pass
        self.check_volumes()
        self.check_access()
        v = self.indexer.version
        if v != self.seen_version and time.time() - self.last_refresh > 1.0:
            self.seen_version = v
            self.last_refresh = time.time()
            self.run_search(refresh=True)
        self.lbl_index.config(text=self.indexer.status)
        self.root.after(100, self.poll)

    def check_access(self):
        """Masaüstü/Belgeler/İndirilenler okunamıyorsa Tam Disk Erişimi için bir kez uyar."""
        if self.cfg.get("fda_warned") or self.indexer.scanning or not self.indexer.denied:
            return
        home = os.path.expanduser("~")
        protected = {os.path.join(home, n) for n in ("Desktop", "Documents", "Downloads")}
        if not (protected & self.indexer.denied):
            return
        self.cfg["fda_warned"] = True
        save_config(self.folder, self.cfg)
        if messagebox.askyesno(
                "Erişim izni gerekli",
                "Everything bazı klasörlere (Masaüstü, Belgeler, İndirilenler…) erişemiyor, "
                "bu yüzden bu klasörlerdeki dosyalar aramada çıkmaz.\n\n"
                "Çözmek için Sistem Ayarları > Gizlilik ve Güvenlik > Tam Disk Erişimi "
                "bölümünde Everything'i açman gerekir. Açtıktan sonra Everything'i kapatıp "
                "yeniden başlat.\n\nAyarları şimdi açayım mı?"):
            open_privacy_settings()

    def check_volumes(self):
        """Harici disk takılınca otomatik ekler; çıkarılıp tekrar takılınca yeniden tarar."""
        now = time.time()
        if now - self._vol_check < 3.0:
            return
        self._vol_check = now
        changed = False
        if self.cfg.get("auto_external", True):
            for p in list_external_volumes():
                if p not in self.cfg["roots"] and p not in self.cfg["ignored_volumes"]:
                    self.cfg["roots"].append(p)
                    changed = True
        state = {r: root_online(r) for r in self.cfg["roots"] if volume_mount_of(r)}
        if self._vol_state is not None:
            for r, online in state.items():
                if online and not self._vol_state.get(r, False):
                    changed = True                       # disk yeniden takıldı
            if set(state) != set(self._vol_state) or any(
                    state[r] != self._vol_state[r] for r in state if r in self._vol_state):
                changed = True
        self._vol_state = state
        if changed:
            save_config(self.folder, self.cfg)
            self.indexer.set_config(self.cfg["roots"], self.cfg["excludes"])
            self.refresh_scopes()

    def handle_result(self, req, rows, total, err):
        if req.gen != self.gen:
            return                                   # eski sorgunun sonucu
        if err:
            self.lbl_count.config(text="⚠ " + err)
            return
        self.total = total
        if rows is not None and rows != self.rows:
            self.fill(rows, keep_view=req.refresh)
        self.update_count_label()

    def update_count_label(self):
        shown = len(self.rows)
        if self.total is None:
            text = f"{fmt_int(shown)}+ nesne (sayılıyor…)"
        elif self.total > shown:
            text = f"{fmt_int(self.total)} nesne — ilk {fmt_int(shown)} gösteriliyor"
        else:
            text = f"{fmt_int(self.total)} nesne"
        self.lbl_count.config(text=text)

    def row_values(self, row):
        name, d, is_dir, size, mtime, ext, btime = row
        icon = ("📁 " if is_dir else "📄 ") if self.use_emoji else ("▸ " if is_dir else "")
        vals = {"name": icon + name, "path": d, "size": "" if is_dir else fmt_size(size),
                "ext": ext, "type": type_text(ext, is_dir), "date": fmt_date(mtime),
                "btime": fmt_date(btime)}
        return tuple(vals[c] for c in COLUMN_ORDER)

    def fill(self, rows, keep_view):
        selected = {os.path.join(r[1], r[0]) for r in self._selected_rows()} if keep_view else set()
        view = self.tree.yview()[0] if keep_view else 0.0
        self.tree.delete(*self.tree.get_children())
        self.rows = rows
        reselect = []
        for i, row in enumerate(rows):
            self.tree.insert("", "end", iid=str(i), values=self.row_values(row))
            if selected and os.path.join(row[1], row[0]) in selected:
                reselect.append(str(i))
        if reselect:
            self.tree.selection_set(reselect)
        self.tree.yview_moveto(view)
        self.update_selection_label()

    def update_selection_label(self):
        rows = self._selected_rows()
        if not rows:
            self.lbl_sel.config(text="")
            return
        total = sum(r[3] for r in rows if not r[2])
        text = f"{fmt_int(len(rows))} nesne seçili"
        if total:
            text += f" · {fmt_size(total)}"
        self.lbl_sel.config(text=text)

    # ======================================================================
    # Seçili öğelerle işlemler
    # ======================================================================
    def _selected_rows(self):
        out = []
        for iid in self.tree.selection():
            try:
                out.append(self.rows[int(iid)])
            except (ValueError, IndexError):
                pass
        return out

    def _paths(self, first_if_none=False):
        rows = self._selected_rows()
        if not rows and first_if_none and self.rows:
            rows = [self.rows[0]]
        return [os.path.join(r[1], r[0]) for r in rows]

    def open_selected(self, first_if_none=False):
        for p in self._paths(first_if_none):
            try:
                open_path(p)
            except OSError as e:
                messagebox.showerror("Açılamadı", str(e))

    def reveal_selected(self):
        for p in self._paths():
            reveal_path(p)

    def get_info(self):
        if sys.platform != "darwin":
            return
        for p in self._paths()[:5]:
            script = ('tell application "Finder" to open information window of '
                      f'(POSIX file "{applescript_escape(p)}" as alias)')
            subprocess.Popen(["osascript", "-e", script,
                              "-e", 'tell application "Finder" to activate'])

    def copy_selected(self, kind):
        rows = self._selected_rows()
        if not rows:
            return
        if kind == "name":
            items = [r[0] for r in rows]
        elif kind == "dir":
            items = [r[1] for r in rows]
        else:
            items = [os.path.join(r[1], r[0]) for r in rows]
        self.root.clipboard_clear()
        self.root.clipboard_append("\n".join(items))

    def trash_selected(self):
        paths = self._paths()
        if not paths:
            return
        if sys.platform != "darwin":
            messagebox.showerror("Desteklenmiyor", "Çöpe taşıma yalnızca macOS'ta çalışır.")
            return
        msg = f"{len(paths)} öğe Çöp Sepeti'ne taşınsın mı?\n\n" + "\n".join(paths[:5])
        if len(paths) > 5:
            msg += "\n…"
        if not messagebox.askyesno("Çöpe taşı", msg):
            return
        items = ", ".join(f'POSIX file "{applescript_escape(p)}"' for p in paths)
        try:
            res = subprocess.run(["osascript", "-e", f'tell application "Finder" to delete {{{items}}}'],
                                 capture_output=True, text=True, timeout=60)
            if res.returncode != 0:
                messagebox.showerror("Çöpe taşınamadı", res.stderr.strip() or "Bilinmeyen hata")
        except (OSError, subprocess.SubprocessError) as e:
            messagebox.showerror("Çöpe taşınamadı", str(e))
        self.indexer.mark_dirty(paths)

    def export_results(self):
        if not self.rows:
            messagebox.showinfo("Dışa aktar", "Dışa aktarılacak sonuç yok.")
            return
        path = filedialog.asksaveasfilename(defaultextension=".csv", initialfile="sonuclar.csv",
                                            filetypes=[("CSV dosyası", "*.csv")])
        if not path:
            return
        try:
            with open(path, "w", newline="", encoding="utf-8-sig") as f:
                w = csv.writer(f)
                w.writerow(["Ad", "Yol", "Boyut (bayt)", "Uzantı", "Tür",
                            "Değiştirilme tarihi", "Oluşturulma tarihi"])
                for name, d, is_dir, size, mtime, ext, btime in self.rows:
                    w.writerow([name, d, "" if is_dir else size, ext, type_text(ext, is_dir),
                                fmt_date(mtime), fmt_date(btime)])
        except OSError as e:
            messagebox.showerror("Dışa aktarılamadı", str(e))

    def select_all(self):
        self.tree.selection_set(self.tree.get_children())
        return "break"

    def invert_selection(self):
        cur = set(self.tree.selection())
        self.tree.selection_set([i for i in self.tree.get_children() if i not in cur])

    def on_double_click(self, event):
        if self.tree.identify_row(event.y):
            self.open_selected()

    def show_menu(self, event):
        region = self.tree.identify_region(event.x, event.y)
        if region in ("heading", "separator"):
            menu = self.col_menu
        else:
            iid = self.tree.identify_row(event.y)
            if iid and iid not in self.tree.selection():
                self.tree.selection_set(iid)
            if not self.tree.selection():
                return
            menu = self.row_menu
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def focus_tree(self, _event=None):
        children = self.tree.get_children()
        if children:
            self.tree.focus_set()
            if not self.tree.selection():
                self.tree.selection_set(children[0])
                self.tree.focus(children[0])
        return "break"

    def focus_entry(self, _event=None):
        self.entry.focus_set()
        self.entry.select_range(0, "end")
        return "break"

    # ======================================================================
    # Yer imleri
    # ======================================================================
    def rebuild_bookmarks_menu(self):
        m = self.bookmarks_menu
        m.delete(0, "end")
        m.add_command(label="Yer İmi Ekle…", accelerator="⌘D", command=self.add_bookmark)
        m.add_command(label="Yer İmlerini Düzenle…", command=self.organize_bookmarks)
        if self.cfg["bookmarks"]:
            m.add_separator()
        for b in self.cfg["bookmarks"]:
            m.add_command(label=b["name"], command=lambda bk=b: self.apply_bookmark(bk))

    def bookmarks_changed(self):
        save_config(self.folder, self.cfg)
        self.rebuild_bookmarks_menu()

    def add_bookmark(self):
        name = simpledialog.askstring("Yer imi ekle", "Yer imi adı:", parent=self.root,
                                      initialvalue=self.query.get() or "Yeni yer imi")
        if not name:
            return
        self.cfg["bookmarks"].append({
            "name": name, "search": self.query.get(), "match_case": self.var_case.get(),
            "match_path": self.var_path.get(), "regex": self.var_regex.get(),
            "whole_word": self.var_word.get(), "diacritics": self.var_diac.get(),
            "filter": self.var_filter.get(), "scope": self.scope_path(),
            "sort": self.sort_col, "desc": self.sort_desc})
        self.bookmarks_changed()
        return "break"

    def apply_bookmark(self, b):
        self.var_case.set(bool(b.get("match_case", False)))
        self.var_path.set(bool(b.get("match_path", False)))
        self.var_regex.set(bool(b.get("regex", False)))
        self.var_word.set(bool(b.get("whole_word", False)))
        self.var_diac.set(bool(b.get("diacritics", False)))
        flt = b.get("filter", "Hepsi")
        self.var_filter.set(flt if flt in FILTERS else "Hepsi")
        scope = b.get("scope", "")
        self.var_scope.set(next((l for l, p in self.scope_map.items() if p == scope), "Her yerde"))
        col = b.get("sort", "name")
        self.sort_col = col if col in COLUMNS else "name"
        self.sort_desc = bool(b.get("desc", False))
        self.update_headings()
        self.query.set(b.get("search", ""))
        self.run_search_now()

    def organize_bookmarks(self):
        BookmarksDialog(self)

    # ======================================================================
    # Pencereler
    # ======================================================================
    def open_options(self, page="general"):
        if self.opts_dialog is not None and self.opts_dialog.alive:
            self.opts_dialog.show(page)
            return
        self.opts_dialog = OptionsDialog(self, page)

    def apply_options(self):
        cfg = self.cfg
        set_result_limit(cfg["result_limit"])
        self.apply_font()
        self.apply_columns()
        self.apply_window_flags()
        self.entry.configure(values=cfg["history"])
        save_config(self.folder, cfg)
        self.indexer.set_config(cfg["roots"], cfg["excludes"], cfg["skip_packages"],
                                cfg["exclude_patterns"], cfg["exclude_hidden"])
        self.refresh_scopes()
        self.schedule_search()

    def show_syntax(self):
        win = tk.Toplevel(self.root)
        win.title("Arama Sözdizimi")
        win.geometry("640x560")
        box = ttk.Frame(win, padding=8)
        box.pack(fill="both", expand=True)
        sb = ttk.Scrollbar(box, orient="vertical")
        text = tk.Text(box, wrap="word", font=("Menlo", 12), padx=8, pady=8,
                       yscrollcommand=sb.set)
        sb.configure(command=text.yview)
        text.insert("1.0", SYNTAX_HELP)
        text.configure(state="disabled")
        text.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

    def show_about(self):
        messagebox.showinfo(
            f"Everything {APP_VERSION} Hakkında",
            f"Everything {APP_VERSION}\n\n"
            "voidtools Everything'den esinlenen, Mac için sıfırdan yazılmış\n"
            "anında dosya/klasör arama programı.\n\n"
            f"İndeks ve ayarlar:\n{self.folder}")

    # ======================================================================
    # Yaşam döngüsü
    # ======================================================================
    def on_close(self):
        try:
            self.cfg["geometry"] = self.root.geometry()
            widths = {}
            for c in COLUMN_ORDER:
                try:
                    widths[c] = int(self.tree.column(c, "width"))
                except (ValueError, tk.TclError):
                    pass
            self.cfg["col_widths"] = widths
            self.cfg["scope"] = self.scope_path()
        except Exception:
            pass
        save_config(self.folder, self.cfg)
        self.indexer.stop()
        self.searcher.stop()
        self.root.destroy()

    def run(self):
        self.root.mainloop()


class BookmarksDialog:
    def __init__(self, app):
        self.app = app
        win = self.win = tk.Toplevel(app.root)
        win.title("Yer İmlerini Düzenle")
        win.geometry("480x360")
        win.transient(app.root)
        box = ttk.Frame(win, padding=10)
        box.pack(fill="both", expand=True)
        self.lb = tk.Listbox(box, exportselection=False, selectmode="browse")
        self.lb.pack(side="left", fill="both", expand=True)
        btns = ttk.Frame(box)
        btns.pack(side="left", fill="y", padx=(8, 0))
        for text, cmd in (("Yeniden Adlandır…", self.rename), ("Sil", self.delete),
                          ("Yukarı Taşı", lambda: self.move(-1)),
                          ("Aşağı Taşı", lambda: self.move(1)), ("Kapat", win.destroy)):
            ttk.Button(btns, text=text, command=cmd).pack(fill="x", pady=2)
        self.reload()

    def reload(self, select=None):
        self.lb.delete(0, "end")
        for b in self.app.cfg["bookmarks"]:
            self.lb.insert("end", b["name"])
        if select is not None and 0 <= select < len(self.app.cfg["bookmarks"]):
            self.lb.selection_set(select)

    def _index(self):
        sel = self.lb.curselection()
        return int(sel[0]) if sel else None

    def rename(self):
        i = self._index()
        if i is None:
            return
        b = self.app.cfg["bookmarks"][i]
        name = simpledialog.askstring("Yeniden adlandır", "Yeni ad:", parent=self.win,
                                      initialvalue=b["name"])
        if name:
            b["name"] = name
            self.app.bookmarks_changed()
            self.reload(i)

    def delete(self):
        i = self._index()
        if i is None:
            return
        del self.app.cfg["bookmarks"][i]
        self.app.bookmarks_changed()
        self.reload(min(i, len(self.app.cfg["bookmarks"]) - 1))

    def move(self, delta):
        i = self._index()
        bm = self.app.cfg["bookmarks"]
        if i is None or not 0 <= i + delta < len(bm):
            return
        bm[i], bm[i + delta] = bm[i + delta], bm[i]
        self.app.bookmarks_changed()
        self.reload(i + delta)


class OptionsDialog:
    """Everything'in Seçenekler penceresi: solda sayfa listesi, sağda sayfa, altta Tamam/İptal/Uygula."""

    PAGES = (("general", "Genel"), ("ui", "Arayüz"), ("home", "Ana Sayfa"),
             ("search", "Arama"), ("results", "Sonuçlar"), ("history", "Geçmiş"))
    INDEX_PAGES = (("disks", "Diskler"), ("folders", "Klasörler"), ("exclude", "Hariç Tut"))

    def __init__(self, app, page="general"):
        self.app = app
        self.alive = True
        self.current = None
        cfg = app.cfg
        home = cfg["home"]
        self.sort_labels = {COLUMNS[c][0]: c for c in COLUMN_ORDER}

        win = self.win = tk.Toplevel(app.root)
        win.title("Seçenekler")
        win.geometry("880x600")
        win.minsize(780, 520)
        win.transient(app.root)
        win.protocol("WM_DELETE_WINDOW", self.close)

        self.v_auto = tk.BooleanVar(value=cfg["auto_external"])
        self.v_top = tk.BooleanVar(value=cfg["always_on_top"])
        self.v_status = tk.BooleanVar(value=cfg["show_status"])
        self.v_font = tk.StringVar(value=str(cfg["font_size"]))
        self.v_syt = tk.BooleanVar(value=cfg["search_as_you_type"])
        self.v_limit = tk.StringVar(value=str(cfg["result_limit"]))
        self.v_hist = tk.BooleanVar(value=cfg["save_history"])
        self.v_pkg = tk.BooleanVar(value=cfg["skip_packages"])
        self.v_hidden = tk.BooleanVar(value=cfg["exclude_hidden"])
        self.col_vars = {c: tk.BooleanVar(value=c in cfg["columns"]) for c in COLUMN_ORDER}
        self.h_search = tk.StringVar(value=home["search"])
        self.h_filter = tk.StringVar(value=home["filter"])
        self.h_sort = tk.StringVar(value=COLUMNS.get(home["sort"], COLUMNS["name"])[0])
        self.h_desc = tk.BooleanVar(value=home["desc"])
        self.h_case = tk.BooleanVar(value=home["match_case"])
        self.h_path = tk.BooleanVar(value=home["match_path"])
        self.h_regex = tk.BooleanVar(value=home["regex"])
        self.h_word = tk.BooleanVar(value=home["whole_word"])
        self.h_diac = tk.BooleanVar(value=home["diacritics"])

        self.disk_rows, self.disk_checked = [], {}
        self.compute_disks()

        outer = ttk.Frame(win, padding=10)
        outer.pack(fill="both", expand=True)
        buttons = ttk.Frame(outer)
        buttons.pack(side="bottom", fill="x", pady=(10, 0))
        ttk.Button(buttons, text="Uygula", command=self.apply).pack(side="right")
        ttk.Button(buttons, text="İptal", command=self.close).pack(side="right", padx=6)
        ttk.Button(buttons, text="Tamam", command=self.ok).pack(side="right")
        body = ttk.Frame(outer)
        body.pack(side="top", fill="both", expand=True)

        self.nav = ttk.Treeview(body, show="tree", selectmode="browse")
        self.nav.column("#0", width=170, stretch=False)
        for pid, title in self.PAGES:
            self.nav.insert("", "end", iid=pid, text=title)
        self.nav.insert("", "end", iid="indexes", text="Dizinler", open=True)
        for pid, title in self.INDEX_PAGES:
            self.nav.insert("indexes", "end", iid=pid, text=title)
        self.nav.pack(side="left", fill="y")
        self.holder = ttk.Frame(body, padding=(14, 0, 0, 0))
        self.holder.pack(side="left", fill="both", expand=True)

        self.frames = {}
        for pid, _title in self.PAGES + self.INDEX_PAGES:
            self.frames[pid] = ttk.Frame(self.holder)
            getattr(self, "_page_" + pid)(self.frames[pid])
        self.nav.bind("<<TreeviewSelect>>", self.on_nav)
        self.show(page)

    # ---- sayfa gezintisi ----------------------------------------------------
    def on_nav(self, _event=None):
        sel = self.nav.selection()
        if sel:
            self.show(sel[0])

    def show(self, pid):
        if pid == "indexes":
            pid = "disks"
        if pid not in self.frames or pid == self.current:
            return
        if self.current:
            self.frames[self.current].pack_forget()
        self.current = pid
        self.frames[pid].pack(fill="both", expand=True)
        if pid == "disks":
            self.refresh_disk_view()
        if self.nav.selection() != (pid,):
            self.nav.selection_set(pid)

    def _title(self, f, text):
        ttk.Label(f, text=text, font=("Helvetica", 16, "bold")).pack(anchor="w", pady=(0, 12))

    def _check(self, f, text, var):
        ttk.Checkbutton(f, text=text, variable=var).pack(anchor="w", pady=3)

    def _list_editor(self, parent, title, items, add_cmd, height=6):
        box = ttk.LabelFrame(parent, text=title, padding=8)
        box.pack(fill="both", expand=True, pady=(0, 8))
        lb = tk.Listbox(box, height=height, exportselection=False, selectmode="extended")
        for item in items:
            lb.insert("end", item)
        lb.pack(side="left", fill="both", expand=True)
        btns = ttk.Frame(box)
        btns.pack(side="left", fill="y", padx=(8, 0))

        def remove():
            for i in reversed(lb.curselection()):
                lb.delete(i)

        ttk.Button(btns, text="Ekle…", command=lambda: add_cmd(lb)).pack(fill="x")
        ttk.Button(btns, text="Kaldır", command=remove).pack(fill="x", pady=(4, 0))
        return lb

    def _add_folder(self, lb):
        d = filedialog.askdirectory(parent=self.win)
        if d and d not in lb.get(0, "end"):
            lb.insert("end", d)

    def _add_pattern(self, lb):
        p = simpledialog.askstring("Ad deseni ekle", "Ad deseni (örn. *.tmp  veya  node_modules):",
                                   parent=self.win)
        if p and p not in lb.get(0, "end"):
            lb.insert("end", p)

    # ---- sayfalar ---------------------------------------------------------------
    def _page_general(self, f):
        self._title(f, "Genel")
        self._check(f, "Takılan harici diskleri otomatik olarak dizine ekle", self.v_auto)
        self._check(f, "Pencereyi her zaman diğer pencerelerin üstünde tut", self.v_top)
        ttk.Separator(f, orient="horizontal").pack(fill="x", pady=14)
        ttk.Label(f, wraplength=520, justify="left",
                  text="Masaüstü, Belgeler, İndirilenler gibi klasörler aramada çıkmıyorsa "
                       "macOS'ta Everything'e Tam Disk Erişimi izni vermen gerekir.").pack(anchor="w")
        ttk.Button(f, text="Tam Disk Erişimi Ayarlarını Aç…",
                   command=open_privacy_settings).pack(anchor="w", pady=8)

    def _page_ui(self, f):
        self._title(f, "Arayüz")
        row = ttk.Frame(f)
        row.pack(anchor="w", pady=3)
        ttk.Label(row, text="Yazı boyutu:").pack(side="left", padx=(0, 8))
        ttk.Spinbox(row, from_=8, to=28, width=5, textvariable=self.v_font).pack(side="left")
        self._check(f, "Durum çubuğunu göster", self.v_status)

    def _page_home(self, f):
        self._title(f, "Ana Sayfa")
        ttk.Label(f, wraplength=520, justify="left",
                  text="Everything her açıldığında bu arama, filtre ve sıralamayla başlar.").pack(anchor="w")
        row = ttk.Frame(f)
        row.pack(fill="x", pady=(10, 4))
        ttk.Label(row, text="Arama:", width=10).pack(side="left")
        ttk.Entry(row, textvariable=self.h_search).pack(side="left", fill="x", expand=True)
        row = ttk.Frame(f)
        row.pack(fill="x", pady=4)
        ttk.Label(row, text="Filtre:", width=10).pack(side="left")
        ttk.Combobox(row, textvariable=self.h_filter, values=list(FILTERS), state="readonly",
                     width=16).pack(side="left")
        row = ttk.Frame(f)
        row.pack(fill="x", pady=4)
        ttk.Label(row, text="Sıralama:", width=10).pack(side="left")
        ttk.Combobox(row, textvariable=self.h_sort, values=list(self.sort_labels), state="readonly",
                     width=20).pack(side="left")
        ttk.Checkbutton(row, text="Azalan", variable=self.h_desc).pack(side="left", padx=10)
        grp = ttk.LabelFrame(f, text="Arama seçenekleri", padding=8)
        grp.pack(fill="x", pady=10)
        for text, var in (("Büyük/küçük harf duyarlı", self.h_case), ("Tam kelime", self.h_word),
                          ("Yolu eşleştir", self.h_path), ("Aksanları eşleştir", self.h_diac),
                          ("Düzenli ifade (regex)", self.h_regex)):
            ttk.Checkbutton(grp, text=text, variable=var).pack(anchor="w")
        ttk.Button(f, text="Şu anki aramayı ana sayfa yap",
                   command=self.home_from_current).pack(anchor="w")

    def home_from_current(self):
        a = self.app
        self.h_search.set(a.query.get())
        self.h_filter.set(a.var_filter.get())
        self.h_sort.set(COLUMNS[a.sort_col][0])
        self.h_desc.set(a.sort_desc)
        self.h_case.set(a.var_case.get())
        self.h_path.set(a.var_path.get())
        self.h_regex.set(a.var_regex.get())
        self.h_word.set(a.var_word.get())
        self.h_diac.set(a.var_diac.get())

    def _page_search(self, f):
        self._title(f, "Arama")
        self._check(f, "Yazdıkça anında ara (kapalıysa Enter'a basınca arar)", self.v_syt)
        ttk.Separator(f, orient="horizontal").pack(fill="x", pady=14)
        ttk.Label(f, wraplength=520, justify="left",
                  text="Joker karakterler, ext:, size:, dm:, regex: gibi arama komutları için "
                       "sözdizimi yardımına bak.").pack(anchor="w")
        ttk.Button(f, text="Arama Sözdizimini Göster", command=self.app.show_syntax).pack(
            anchor="w", pady=8)

    def _page_results(self, f):
        self._title(f, "Sonuçlar")
        row = ttk.Frame(f)
        row.pack(anchor="w", pady=3)
        ttk.Label(row, text="En fazla gösterilecek sonuç:").pack(side="left", padx=(0, 8))
        ttk.Combobox(row, textvariable=self.v_limit, width=8,
                     values=["1000", "2000", "5000", "10000", "20000"]).pack(side="left")
        grp = ttk.LabelFrame(f, text="Görünecek sütunlar (Ad her zaman görünür)", padding=8)
        grp.pack(fill="x", pady=12)
        for c in COLUMN_ORDER[1:]:
            ttk.Checkbutton(grp, text=COLUMNS[c][0], variable=self.col_vars[c]).pack(anchor="w")

    def _page_history(self, f):
        self._title(f, "Geçmiş")
        self._check(f, "Arama geçmişini kaydet", self.v_hist)
        ttk.Button(f, text="Arama Geçmişini Temizle", command=self.app.clear_history).pack(
            anchor="w", pady=8)

    def _page_disks(self, f):
        self._title(f, "Dizinler › Diskler")
        ttk.Label(f, wraplength=560, justify="left",
                  text="Dizine eklenecek diskleri işaretle (☑ üzerine tıkla). Takılı olmayan "
                       "disklerin kayıtları saklanır. Sistem diskini işaretlersen tüm Mac "
                       "taranır, ilk tarama uzun sürebilir.").pack(anchor="w", pady=(0, 8))
        cols = ("on", "name", "path", "fs", "size", "free", "state")
        self.disk_tv = ttk.Treeview(f, columns=cols, show="headings", selectmode="browse", height=9)
        spec = {"on": ("", 36, "center"), "name": ("Disk", 140, "w"), "path": ("Konum", 190, "w"),
                "fs": ("Biçim", 60, "w"), "size": ("Boyut", 70, "e"), "free": ("Boş", 70, "e"),
                "state": ("Durum", 190, "w")}
        for c in cols:
            title, width, anchor = spec[c]
            self.disk_tv.heading(c, text=title)
            self.disk_tv.column(c, width=width, anchor=anchor, stretch=c in ("path", "state"))
        self.disk_tv.pack(fill="both", expand=True)
        self.disk_tv.bind("<Button-1>", self._disk_click)
        self.disk_tv.bind("<Double-1>", self._disk_double)
        self.disk_tv.bind("<space>", self._disk_space)
        row = ttk.Frame(f)
        row.pack(fill="x", pady=8)
        ttk.Button(row, text="Tümünü İşaretle", command=lambda: self.check_all(True)).pack(side="left")
        ttk.Button(row, text="İşaretleri Kaldır", command=lambda: self.check_all(False)).pack(
            side="left", padx=6)
        ttk.Button(row, text="Listeyi Yenile", command=self.reload_disks).pack(side="left")

    def _page_folders(self, f):
        self._title(f, "Dizinler › Klasörler")
        ttk.Label(f, wraplength=560, justify="left",
                  text="Disklerin dışında ayrıca dizine eklenecek klasörler.").pack(anchor="w", pady=(0, 8))
        paths = {d["path"] for d in self.disk_rows}
        self.lb_roots = self._list_editor(
            f, "Dizine eklenecek klasörler",
            [r for r in self.app.cfg["roots"] if r not in paths], self._add_folder, height=10)
        ttk.Button(f, text="Şimdi Yeniden Tara", command=self.app.indexer.rescan_full).pack(anchor="w")

    def _page_exclude(self, f):
        self._title(f, "Dizinler › Hariç Tut")
        cfg = self.app.cfg
        self._check(f, "Gizli dosya ve klasörleri hariç tut (adı . ile başlayanlar)", self.v_hidden)
        self._check(f, "Paket içeriklerini (.app, .photoslibrary…) dizine ekleme", self.v_pkg)
        self.lb_excl = self._list_editor(f, "Hariç tutulacak klasörler", cfg["excludes"],
                                         self._add_folder, height=5)
        self.lb_patterns = self._list_editor(f, "Hariç tutulacak dosya/klasör adları (joker karakterli)",
                                             cfg["exclude_patterns"], self._add_pattern, height=5)

    # ---- diskler ------------------------------------------------------------------
    def compute_disks(self):
        cfg = self.app.cfg
        rows = list_disks()
        known = {d["path"] for d in rows}
        for r in cfg["roots"]:
            if volume_mount_of(r) == r and r not in known:      # takılı olmayan harici disk
                rows.append({"name": os.path.basename(r), "path": r, "fs": "", "total": 0,
                             "free": 0, "boot": False, "offline": True})
        old = self.disk_checked
        self.disk_rows = rows
        self.disk_checked = {d["path"]: old.get(d["path"], d["path"] in cfg["roots"]) for d in rows}

    def reload_disks(self):
        self.compute_disks()
        self.refresh_disk_view()

    def check_all(self, on):
        for p in self.disk_checked:
            self.disk_checked[p] = on
        self.refresh_disk_view()

    def refresh_disk_view(self):
        tv = self.disk_tv
        tv.delete(*tv.get_children())
        folders = list(self.lb_roots.get(0, "end"))
        for i, d in enumerate(self.disk_rows):
            on = self.disk_checked[d["path"]]
            if d.get("offline"):
                state = "Bağlı değil"
            elif d["boot"]:
                state = "Sistem diski"
            else:
                state = "Bağlı"
            if not on and any(r != d["path"] and path_under(r, d["path"]) for r in folders):
                state += " · yalnızca seçili klasörler"
            total = fmt_size(d["total"]) if d["total"] else ""
            free = fmt_size(d["free"]) if d["total"] else ""
            tv.insert("", "end", iid=str(i),
                      values=("☑" if on else "☐", d["name"], d["path"], d["fs"], total, free, state))

    def toggle_disk(self, iid):
        d = self.disk_rows[int(iid)]
        self.disk_checked[d["path"]] = not self.disk_checked[d["path"]]
        self.refresh_disk_view()
        self.disk_tv.selection_set(iid)

    def _disk_click(self, event):
        iid = self.disk_tv.identify_row(event.y)
        if iid and self.disk_tv.identify_column(event.x) == "#1":
            self.toggle_disk(iid)

    def _disk_double(self, event):
        iid = self.disk_tv.identify_row(event.y)
        if iid and self.disk_tv.identify_column(event.x) != "#1":
            self.toggle_disk(iid)

    def _disk_space(self, _event=None):
        sel = self.disk_tv.selection()
        if sel:
            self.toggle_disk(sel[0])
        return "break"

    # ---- uygula / kapat --------------------------------------------------------------
    def apply(self):
        app = self.app
        cfg = app.cfg
        cfg["auto_external"] = bool(self.v_auto.get())
        cfg["always_on_top"] = bool(self.v_top.get())
        cfg["show_status"] = bool(self.v_status.get())
        try:
            cfg["font_size"] = min(max(int(self.v_font.get()), 8), 28)
        except ValueError:
            pass
        try:
            cfg["result_limit"] = min(max(int(self.v_limit.get()), 100), 50000)
        except ValueError:
            pass
        cfg["search_as_you_type"] = bool(self.v_syt.get())
        cfg["save_history"] = bool(self.v_hist.get())
        cfg["skip_packages"] = bool(self.v_pkg.get())
        cfg["exclude_hidden"] = bool(self.v_hidden.get())
        cfg["columns"] = [c for c in COLUMN_ORDER if c == "name" or self.col_vars[c].get()]
        cfg["excludes"] = list(self.lb_excl.get(0, "end"))
        cfg["exclude_patterns"] = list(self.lb_patterns.get(0, "end"))

        folders = list(self.lb_roots.get(0, "end"))
        checked = [p for p, on in self.disk_checked.items() if on]
        cfg["roots"] = folders + [p for p in checked if p not in folders]
        ignored = set(cfg["ignored_volumes"])
        for p, on in self.disk_checked.items():
            if p == os.sep:
                continue
            if on:
                ignored.discard(p)
            else:
                ignored.add(p)            # kaldırılan disk kendiliğinden tekrar eklenmesin
        cfg["ignored_volumes"] = sorted(ignored)

        cfg["home"] = {
            "search": self.h_search.get(),
            "filter": self.h_filter.get() if self.h_filter.get() in FILTERS else "Hepsi",
            "sort": self.sort_labels.get(self.h_sort.get(), "name"),
            "desc": bool(self.h_desc.get()), "match_case": bool(self.h_case.get()),
            "match_path": bool(self.h_path.get()), "regex": bool(self.h_regex.get()),
            "whole_word": bool(self.h_word.get()), "diacritics": bool(self.h_diac.get())}
        app.apply_options()
        self.compute_disks()

    def ok(self):
        self.apply()
        self.close()

    def close(self):
        self.alive = False
        self.win.destroy()


def main():
    if tk is None:
        print("tkinter bulunamadı.\n"
              "  - python.org'dan Python kurduysan tkinter hazır gelir.\n"
              "  - Homebrew Python kullanıyorsan: brew install python-tk")
        sys.exit(1)
    App().run()


if __name__ == "__main__":
    main()
