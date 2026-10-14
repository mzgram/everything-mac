#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Everything (Mac) - dosya ve klasörleri anında bulun.

voidtools Everything'in Mac için, sıfırdan yazılmış işlevsel bir benzeri.
Yalnızca Python standart kütüphanesini kullanır (tkinter + sqlite3).
İsteğe bağlı: `pip3 install watchdog` -> gerçek zamanlı güncelleme (FSEvents).

Çalıştırma:   python3 everything_mac.py

Arama sözdizimi (Everything'e benzer):
  rapor 2024          iki kelime de adda geçsin (AND)
  "bütçe planı"       tırnak içindeki ifade tek parça
  foo|bar             foo VEYA bar
  !taslak             "taslak" geçmesin
  *.pdf   a?c*        joker karakterler (adın tamamıyla eşleşir)
  ext:mp4;mov         uzantıya göre
  size:>100mb         boyuta göre (>, <, >=, <=, =; kb mb gb tb)
  folder:  file:      yalnızca klasörler / yalnızca dosyalar
  path:belgeler       yolda ara
  Documents/rapor     "/" içeren terimler yolda aranır
  regex:^IMG_\\d+     düzenli ifade (veya "Regex" kutusu)
"""

import json
import os
import queue
import re
import sqlite3
import subprocess
import sys
import threading
import time
import unicodedata
from collections import namedtuple
from datetime import datetime
from functools import lru_cache

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk
except ImportError:  # Homebrew Python'da: brew install python-tk
    tk = None

APP_NAME = "EverythingMac"
SCHEMA_VERSION = 1
RESULT_LIMIT = 2000          # ekranda gösterilecek en fazla satır
POLL_SECONDS = 60            # watchdog yoksa periyodik tarama aralığı
BATCH_ROWS = 5000            # bu kadar satırda bir commit (sonuçlar canlı görünsün)

SKIP_NAMES = {".Spotlight-V100", ".fseventsd", ".Trashes",
              ".DocumentRevisions-V100", ".TemporaryItems", ".vol"}
SKIP_PATHS = {"/System/Volumes", "/dev", "/private/var/vm", "/proc"}


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


def fold(s):
    """Büyük/küçük harf ve Unicode biçimi (NFC/NFD) fark etmeyen karşılaştırma anahtarı.
    Türkçe için İ/ı -> i eşlemesi yapılır; böylece 'istanbul', 'İstanbul' ve
    'Istanbul' birbirini bulur. (macOS dosya adları sıklıkla NFD olarak gelir.)"""
    s = unicodedata.normalize("NFC", s)
    return s.replace("İ", "i").replace("ı", "i").lower()


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


def default_config():
    home = os.path.expanduser("~")
    return {"roots": [home], "excludes": [os.path.join(home, "Library")]}


def load_config(folder):
    path = os.path.join(folder, "config.json")
    cfg = default_config()
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data.get("roots"), list):
            cfg["roots"] = [str(x) for x in data["roots"]]
        if isinstance(data.get("excludes"), list):
            cfg["excludes"] = [str(x) for x in data["excludes"]]
    except (OSError, ValueError):
        pass
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


def reveal_path(path):
    if sys.platform == "darwin":
        subprocess.Popen(["open", "-R", path])
    else:
        open_path(os.path.dirname(path))


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
    mtime  REAL NOT NULL
);
CREATE INDEX IF NOT EXISTS files_dir ON files(dir_id);
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
    return conn


# --------------------------------------------------------------------------
# İndeksleyici
# --------------------------------------------------------------------------

class Indexer(threading.Thread):
    """Klasörleri tarar, SQLite'a yazar ve değişiklikleri izler."""

    def __init__(self, db_path, data_folder, roots, excludes):
        super().__init__(daemon=True)
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
        self.roots = [os.path.abspath(os.path.expanduser(r)) for r in roots if r]
        self.excludes = [os.path.abspath(os.path.expanduser(e)) for e in excludes if e]
        self.excludes.append(self.data_folder)
        self.excludes.extend(SKIP_PATHS)

    def set_config(self, roots, excludes):
        with self.lock:
            self._set_paths(roots, excludes)
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
        return f"Hazır · {fmt_int(self.count)} öğe · izleme: {self.watch_mode}"

    def _excluded(self, path):
        for e in self.excludes:
            if path == e or path.startswith(e.rstrip(os.sep) + os.sep):
                return True
        return False

    def _under_roots(self, path):
        for r in self.roots:
            if path == r or path.startswith(r.rstrip(os.sep) + os.sep):
                return True
        return False

    # ---- veri işlemleri --------------------------------------------------
    def _list_dir(self, d):
        """[(name, lname, is_dir, size, mtime)] ya da okunamazsa None."""
        out = []
        try:
            with os.scandir(d) as it:
                for e in it:
                    name = e.name
                    if name in SKIP_NAMES or self._excluded(e.path):
                        continue
                    try:
                        is_dir = e.is_dir(follow_symlinks=False)
                        st = e.stat(follow_symlinks=False)
                        out.append((name, fold(name), 1 if is_dir else 0,
                                    0 if is_dir else st.st_size, st.st_mtime))
                    except OSError:
                        out.append((name, fold(name), 0, 0, 0.0))
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
                    "INSERT INTO files(dir_id, name, lname, is_dir, size, mtime) VALUES(?,?,?,?,?,?)",
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
        try:
            self._prune()
            for r in list(self.roots):
                if self.stop_evt.is_set():
                    break
                if os.path.isdir(r):
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
                if os.path.isdir(r):
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
                    dirty, self.dirty = self.dirty, set()
                if reconf or full:
                    self.full_pass(force=full)
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
                            if self._under_roots(d) and not self._excluded(d):
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


Req = namedtuple("Req", "gen text match_case match_path regex sort_col sort_desc refresh")
Compiled = namedtuple("Compiled", "select count params")

SIZE_RE = re.compile(r"^(>=|<=|>|<|=)?\s*([0-9]+(?:[.,][0-9]+)?)\s*([a-zA-Z]*)$")
UNITS = {"": 1, "b": 1, "k": 1024, "kb": 1024, "m": 1024 ** 2, "mb": 1024 ** 2,
         "g": 1024 ** 3, "gb": 1024 ** 3, "t": 1024 ** 4, "tb": 1024 ** 4}
SORTS = {"name": "f.lname {d}", "path": "d.lpath {d}, f.lname {d}",
         "size": "f.size {d}, f.lname", "date": "f.mtime {d}, f.lname"}


def _term_cond(term, match_case, use_path):
    if "/" in term:
        use_path = True
    if match_case:
        t = unicodedata.normalize("NFC", term)
        target = "(d.path || '/' || f.name)" if use_path else "f.name"
    else:
        t = fold(term)
        target = "(d.lpath || '/' || f.lname)" if use_path else "f.lname"
    if "*" in t or "?" in t:
        return f"{target} GLOB ?", [t.replace("[", "[[]")], use_path
    return f"instr({target}, ?) > 0", [t], use_path


def build_where(text, match_case=False, match_path=False, regex=False):
    """Arama metnini SQL WHERE parçasına çevirir -> (where, params, needs_dirs)."""
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
        else:
            if not quoted and low.startswith("path:") and len(tok) > 5:
                tok, force_path = tok[5:], True
            alts = tok.split("|") if (not quoted and "|" in tok) else [tok]
            parts = []
            for a in alts:
                if not a:
                    continue
                sql, sp, nd = _term_cond(a, match_case, match_path or force_path)
                parts.append(sql)
                p += sp
                needs_dirs = needs_dirs or nd
            if not parts:
                continue
            c = " OR ".join(parts)

        conds.append(f"NOT ({c})" if neg else f"({c})")
        params += p

    return (" AND ".join(conds) if conds else "1"), params, needs_dirs


def compile_query(req):
    where, params, needs_dirs = build_where(req.text, req.match_case, req.match_path, req.regex)
    order = ""
    if req.sort_col in SORTS:
        order = " ORDER BY " + SORTS[req.sort_col].format(d="DESC" if req.sort_desc else "ASC")
    select = ("SELECT f.name, d.path, f.is_dir, f.size, f.mtime "
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

class App:
    COLS = ("name", "path", "size", "date")
    HEAD = {"name": "Ad", "path": "Yol", "size": "Boyut", "date": "Değiştirilme tarihi"}

    def __init__(self):
        self.folder = data_dir()
        self.db_path = os.path.join(self.folder, "index.db")
        self.cfg = load_config(self.folder)

        self.indexer = Indexer(self.db_path, self.folder, self.cfg["roots"], self.cfg["excludes"])
        self.out = queue.Queue()
        self.searcher = Searcher(self.db_path, self.out)

        self.gen = 0
        self.rows = []
        self.total = None
        self.sort_col = None
        self.sort_desc = False
        self.seen_version = -1
        self.last_refresh = 0.0
        self.search_job = None

        self._build_ui()
        self.searcher.start()
        self.indexer.start()
        self.run_search()
        self.root.after(100, self.poll)

    # ---- arayüz kurulumu -------------------------------------------------
    def _build_ui(self):
        self.root = root = tk.Tk()
        root.title("Everything")
        root.geometry("1100x650")
        root.minsize(700, 400)
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        try:   # eski Tk (8.5 / <8.6.10) emoji çizerken sorun çıkarabilir
            ver = tuple(int(x) for x in str(root.tk.call("info", "patchlevel")).split(".")[:3])
            self.use_emoji = ver >= (8, 6, 10)
        except Exception:
            self.use_emoji = False

        menubar = tk.Menu(root)
        filemenu = tk.Menu(menubar, tearoff=0)
        filemenu.add_command(label="Klasör ayarları…", command=self.open_settings)
        filemenu.add_command(label="Tam yeniden tara", command=self.indexer.rescan_full)
        filemenu.add_separator()
        filemenu.add_command(label="Çıkış", command=self.on_close)
        menubar.add_cascade(label="Dosya", menu=filemenu)
        root.config(menu=menubar)

        top = ttk.Frame(root, padding=(8, 8, 8, 4))
        top.pack(fill="x")
        self.query = tk.StringVar()
        self.entry = ttk.Entry(top, textvariable=self.query, font=("Helvetica", 16))
        self.entry.pack(fill="x")
        self.query.trace_add("write", lambda *_: self.schedule_search())

        opts = ttk.Frame(top)
        opts.pack(fill="x", pady=(4, 0))
        self.var_case = tk.BooleanVar(value=False)
        self.var_path = tk.BooleanVar(value=False)
        self.var_regex = tk.BooleanVar(value=False)
        for text, var in (("Büyük/küçük harf duyarlı", self.var_case),
                          ("Yolu eşleştir", self.var_path),
                          ("Düzenli ifade (regex)", self.var_regex)):
            ttk.Checkbutton(opts, text=text, variable=var,
                            command=self.schedule_search).pack(side="left", padx=(0, 14))

        body = ttk.Frame(root)
        body.pack(fill="both", expand=True, padx=8, pady=4)
        self.tree = ttk.Treeview(body, columns=self.COLS, show="headings", selectmode="extended")
        widths = {"name": 300, "path": 480, "size": 90, "date": 150}
        for col in self.COLS:
            self.tree.heading(col, text=self.HEAD[col], command=lambda c=col: self.sort_by(c))
            self.tree.column(col, width=widths[col], anchor="e" if col == "size" else "w",
                             stretch=col in ("name", "path"))
        vsb = ttk.Scrollbar(body, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

        bar = ttk.Frame(root, padding=(8, 2, 8, 6))
        bar.pack(fill="x")
        self.lbl_left = ttk.Label(bar, text="")
        self.lbl_left.pack(side="left")
        self.lbl_right = ttk.Label(bar, text="")
        self.lbl_right.pack(side="right")

        self.menu = tk.Menu(root, tearoff=0)
        self.menu.add_command(label="Aç", command=self.open_selected)
        self.menu.add_command(label="Finder'da göster", command=self.reveal_selected)
        self.menu.add_separator()
        self.menu.add_command(label="Yolu kopyala", command=lambda: self.copy_selected("path"))
        self.menu.add_command(label="Adı kopyala", command=lambda: self.copy_selected("name"))

        def bind(widget, seq, fn):
            try:
                widget.bind(seq, fn)
            except tk.TclError:          # bu platformda olmayan tuş adı
                pass

        bind(self.entry, "<Return>", lambda e: self.open_selected(first_if_none=True))
        bind(self.entry, "<Escape>", lambda e: self.query.set(""))
        bind(self.entry, "<Down>", self.focus_tree)
        bind(self.tree, "<Return>", lambda e: self.open_selected())
        bind(self.tree, "<Double-1>", self.on_double_click)
        bind(self.tree, "<Command-c>", lambda e: self.copy_selected("path"))
        bind(self.tree, "<Control-c>", lambda e: self.copy_selected("path"))
        for seq in ("<Button-2>", "<Button-3>", "<Control-Button-1>"):
            bind(self.tree, seq, self.show_menu)
        bind(root, "<Command-f>", self.focus_entry)
        bind(root, "<Control-f>", self.focus_entry)
        self.entry.focus_set()

    # ---- arama ------------------------------------------------------------
    def schedule_search(self):
        if self.search_job is not None:
            self.root.after_cancel(self.search_job)
        self.search_job = self.root.after(60, self.run_search)

    def run_search(self, refresh=False):
        self.search_job = None
        self.gen += 1
        self.searcher.submit(Req(self.gen, self.query.get(), self.var_case.get(),
                                 self.var_path.get(), self.var_regex.get(),
                                 self.sort_col, self.sort_desc, refresh))

    def sort_by(self, col):
        if self.sort_col == col:
            self.sort_desc = not self.sort_desc
        else:
            self.sort_col, self.sort_desc = col, False
        for c in self.COLS:
            mark = (" ▼" if self.sort_desc else " ▲") if c == self.sort_col else ""
            self.tree.heading(c, text=self.HEAD[c] + mark)
        self.run_search()

    def poll(self):
        try:
            while True:
                self.handle_result(*self.out.get_nowait())
        except queue.Empty:
            pass
        v = self.indexer.version
        if v != self.seen_version and time.time() - self.last_refresh > 1.0:
            self.seen_version = v
            self.last_refresh = time.time()
            self.run_search(refresh=True)
        self.lbl_right.config(text=self.indexer.status)
        self.root.after(100, self.poll)

    def handle_result(self, req, rows, total, err):
        if req.gen != self.gen:
            return                                   # eski sorgunun sonucu
        if err:
            self.lbl_left.config(text="⚠ " + err)
            return
        if rows is not None:
            self.total = total
            if rows != self.rows:
                self.fill(rows, keep_view=req.refresh)
        else:
            self.total = total
        self.update_count_label()

    def update_count_label(self):
        shown = len(self.rows)
        if self.total is None:
            text = f"{fmt_int(shown)}+ sonuç (sayılıyor…)"
        elif self.total > shown:
            text = f"{fmt_int(self.total)} sonuç — ilk {fmt_int(shown)} gösteriliyor"
        else:
            text = f"{fmt_int(self.total)} sonuç"
        self.lbl_left.config(text=text)

    def fill(self, rows, keep_view):
        selected = {os.path.join(r[1], r[0]) for r in self._selected_rows()} if keep_view else set()
        view = self.tree.yview()[0] if keep_view else 0.0
        self.tree.delete(*self.tree.get_children())
        self.rows = rows
        reselect = []
        for i, (name, d, is_dir, size, mtime) in enumerate(rows):
            icon = ("📁 " if is_dir else "📄 ") if self.use_emoji else ("▸ " if is_dir else "")
            self.tree.insert("", "end", iid=str(i),
                             values=(icon + name, d, "" if is_dir else fmt_size(size), fmt_date(mtime)))
            if selected and os.path.join(d, name) in selected:
                reselect.append(str(i))
        if reselect:
            self.tree.selection_set(reselect)
        self.tree.yview_moveto(view)

    # ---- seçili öğelerle işlemler -------------------------------------------
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

    def copy_selected(self, what):
        rows = self._selected_rows()
        if not rows:
            return
        items = [os.path.join(r[1], r[0]) if what == "path" else r[0] for r in rows]
        self.root.clipboard_clear()
        self.root.clipboard_append("\n".join(items))

    def on_double_click(self, event):
        if self.tree.identify_row(event.y):
            self.open_selected()

    def show_menu(self, event):
        iid = self.tree.identify_row(event.y)
        if iid and iid not in self.tree.selection():
            self.tree.selection_set(iid)
        if self.tree.selection():
            try:
                self.menu.tk_popup(event.x_root, event.y_root)
            finally:
                self.menu.grab_release()

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

    # ---- ayarlar -------------------------------------------------------------
    def open_settings(self):
        win = tk.Toplevel(self.root)
        win.title("Klasör ayarları")
        win.transient(self.root)
        win.geometry("560x430")
        box = ttk.Frame(win, padding=10)
        box.pack(fill="both", expand=True)

        def make_list(title, items):
            frame = ttk.LabelFrame(box, text=title, padding=6)
            frame.pack(fill="both", expand=True, pady=4)
            lb = tk.Listbox(frame, height=6, exportselection=False)
            for item in items:
                lb.insert("end", item)
            lb.pack(side="left", fill="both", expand=True)
            btns = ttk.Frame(frame)
            btns.pack(side="left", padx=(6, 0), fill="y")

            def add():
                d = filedialog.askdirectory(parent=win)
                if d and d not in lb.get(0, "end"):
                    lb.insert("end", d)

            def remove():
                for i in reversed(lb.curselection()):
                    lb.delete(i)

            ttk.Button(btns, text="Ekle…", command=add).pack(fill="x")
            ttk.Button(btns, text="Kaldır", command=remove).pack(fill="x", pady=(4, 0))
            return lb

        lb_roots = make_list("İndekslenecek klasörler", self.cfg["roots"])
        lb_excl = make_list("Hariç tutulacak klasörler", self.cfg["excludes"])

        def apply():
            self.cfg["roots"] = list(lb_roots.get(0, "end"))
            self.cfg["excludes"] = list(lb_excl.get(0, "end"))
            save_config(self.folder, self.cfg)
            self.indexer.set_config(self.cfg["roots"], self.cfg["excludes"])
            win.destroy()

        row = ttk.Frame(box)
        row.pack(fill="x", pady=(8, 0))
        ttk.Button(row, text="Kaydet ve yeniden tara", command=apply).pack(side="right")
        ttk.Button(row, text="İptal", command=win.destroy).pack(side="right", padx=(0, 6))

    # ---- yaşam döngüsü ----------------------------------------------------------
    def on_close(self):
        self.indexer.stop()
        self.searcher.stop()
        self.root.destroy()

    def run(self):
        self.root.mainloop()


def main():
    if tk is None:
        print("tkinter bulunamadı.\n"
              "  - python.org'dan Python kurduysan tkinter hazır gelir.\n"
              "  - Homebrew Python kullanıyorsan: brew install python-tk")
        sys.exit(1)
    App().run()


if __name__ == "__main__":
    main()
