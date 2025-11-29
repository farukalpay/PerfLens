# pip install PySide6
"""
PerfLens — Visual Python Performance Studio (single-file app.py)

A visual-first profiling studio built with PySide6 + Python stdlib:
- Zero-input demo session on launch (real workload: JSON + image-ish array work + async IO + sqlite)
- Visual insights: interactive flame graph (sampling stacks), timeline trace (zoom/brush),
  memory heatmap (tracemalloc checkpoints + diffs), and hot-path call graph
- Profile your own code: “Profile Script…”, “Profile Function…”
- Diff Mode: compare Run A vs Run B (CPU flame + memory diffs + moved hotspots)
- Optimization Coach: explainable heuristics (N+1 queries, redundant JSON parsing, regex suspects,
  too many allocations, sequential awaits, etc.) with clickable focus jumps
- Polished UX: command palette (Ctrl/Cmd+K), search everywhere, bookmarks, shareable perflens:// links,
  dark/light theme, tooltips with glossary, session save/load (deterministic JSON), export HTML report

Notes:
- Uses stdlib tools: cProfile + pstats + tracemalloc + sys._current_frames sampling timers,
  plus optional “Deep Trace (sys.setprofile)” rerun.
- UI stays responsive via background worker threads, cancellation, throttled rendering, bounded caches.
"""

from __future__ import annotations

import asyncio
import base64
import cProfile
import hashlib
import io
import json
import os
import pstats
import random
import re
import sqlite3
import sys
import tempfile
import threading
import time
import traceback
import types
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Tuple
from urllib.parse import parse_qs, quote, unquote, urlencode, urlparse

from PySide6.QtCore import (
    QAbstractTableModel,
    QByteArray,
    QEvent,
    QMimeData,
    QModelIndex,
    QObject,
    QPointF,
    QRectF,
    QSettings,
    QSignalBlocker,
    QSize,
    Qt,
    QThread,
    QTimer,
    Signal,
)
from PySide6.QtGui import (
    QAction,
    QColor,
    QCursor,
    QFont,
    QFontMetrics,
    QIcon,
    QKeySequence,
    QPainter,
    QPainterPath,
    QPen,
    QPixmap,
)
from PySide6.QtWidgets import (
    QApplication,
    QCheckBox,
    QComboBox,
    QDialog,
    QFileDialog,
    QFormLayout,
    QFrame,
    QGroupBox,
    QHBoxLayout,
    QLabel,
    QLineEdit,
    QListWidget,
    QListWidgetItem,
    QMainWindow,
    QMenu,
    QMessageBox,
    QPushButton,
    QScrollArea,
    QSizePolicy,
    QSplitter,
    QStatusBar,
    QTabWidget,
    QTableView,
    QTextEdit,
    QToolButton,
    QVBoxLayout,
    QWidget,
)

APP_NAME = "PerfLens"
APP_VERSION = "1.0.0"

# -------------------------- Theme --------------------------

DARK = {
    "bg": "#050c1e",
    "panel": "#0d1b38",
    "panel2": "#0a152b",
    "stroke": "#1f2c4f",
    "grid": "#172546",
    "text": "#f5f7ff",
    "muted": "#95a2c7",
    "accent": "#6f9dff",
    "accent2": "#57f4c3",
    "warn": "#ffc15a",
    "bad": "#ff6482",
    "good": "#24e5a1",
    "flame_cold": "#38a1ff",
    "flame_warm": "#f2a65a",
    "flame_hot": "#ff5c8d",
    "shadow": "#01030a90",
    "chip": "#101e3d",
}
LIGHT = {
    "bg": "#f4f6fa",
    "panel": "#ffffff",
    "panel2": "#edf1fb",
    "stroke": "#d5deff",
    "grid": "#dfe6fb",
    "text": "#0c1b2f",
    "muted": "#5c6373",
    "accent": "#4b61ff",
    "accent2": "#00c4a6",
    "warn": "#c06500",
    "bad": "#e53a4d",
    "good": "#059669",
    "flame_cold": "#4b65ff",
    "flame_warm": "#f59e0b",
    "flame_hot": "#f43f5e",
    "shadow": "#0f172a30",
    "chip": "#e2e8ff",
}


def _qcolor(hex_or_name: str) -> QColor:
    return QColor(hex_or_name)


def _blend(a: QColor, b: QColor, t: float) -> QColor:
    t = max(0.0, min(1.0, t))
    return QColor(
        int(a.red() + (b.red() - a.red()) * t),
        int(a.green() + (b.green() - a.green()) * t),
        int(a.blue() + (b.blue() - a.blue()) * t),
        int(a.alpha() + (b.alpha() - a.alpha()) * t),
    )


def _human_ms(s: float) -> str:
    ms = s * 1000.0
    if ms < 1:
        return f"{ms:.2f}ms"
    if ms < 10:
        return f"{ms:.2f}ms"
    if ms < 100:
        return f"{ms:.1f}ms"
    if ms < 1000:
        return f"{ms:.0f}ms"
    return f"{ms/1000.0:.2f}s"


def _human_bytes(n: int) -> str:
    if n < 1024:
        return f"{n} B"
    for unit in ["KB", "MB", "GB", "TB"]:
        n /= 1024.0
        if n < 1024.0:
            return f"{n:.2f} {unit}"
    return f"{n:.2f} PB"


def _short_file(path: str) -> str:
    try:
        return Path(path).name
    except Exception:
        return path or "<unknown>"


def _stable_json_dumps(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


# -------------------------- Session Models --------------------------

@dataclass(frozen=True)
class StackFrame:
    function: str
    filename: str
    lineno: int

    @property
    def key(self) -> str:
        return f"{self.function} ({_short_file(self.filename)}:{self.lineno})"

    @property
    def full(self) -> str:
        return f"{self.function} — {self.filename}:{self.lineno}"


@dataclass
class ProfileSample:
    t: float
    dt: float
    stack: List[StackFrame]
    category: str = "cpu"


@dataclass
class TimelineSpan:
    span_id: str
    name: str
    start: float
    end: float
    category: str
    depth: int = 0
    meta: Dict[str, Any] = field(default_factory=dict)

    @property
    def dur(self) -> float:
        return max(0.0, self.end - self.start)


@dataclass
class MemoryPoint:
    t: float
    current: int
    peak: int
    top: List[Dict[str, Any]] = field(default_factory=list)  # [{filename,lineno,size,count}]
    label: str = ""

    @property
    def mb(self) -> float:
        return self.current / (1024 * 1024)


@dataclass
class FlameNode:
    name: str
    value: float = 0.0
    self_value: float = 0.0
    frame: Optional[StackFrame] = None
    children: Dict[str, "FlameNode"] = field(default_factory=dict)

    def child(self, key: str, display: str, frame: Optional[StackFrame]) -> "FlameNode":
        n = self.children.get(key)
        if n is None:
            n = FlameNode(name=display, frame=frame)
            self.children[key] = n
        return n

    def iter_nodes(self, path: Tuple[str, ...] = ()) -> Iterable[Tuple[Tuple[str, ...], "FlameNode"]]:
        p = path + (self.name,)
        yield p, self
        for _, c in sorted(self.children.items(), key=lambda kv: kv[1].value, reverse=True):
            yield from c.iter_nodes(p)


@dataclass
class HotPathEdge:
    src: str
    dst: str
    weight: float


@dataclass
class Suggestion:
    severity: str  # critical|warning|info
    title: str
    description: str
    evidence: str
    action: str
    focus_link: str = ""
    category: str = "general"


@dataclass
class Bookmark:
    name: str
    link: str
    note: str = ""
    created_at: float = field(default_factory=time.time)


@dataclass
class ProfileSession:
    session_id: str
    name: str
    created_at: float
    meta: Dict[str, Any] = field(default_factory=dict)

    samples: List[ProfileSample] = field(default_factory=list)
    spans: List[TimelineSpan] = field(default_factory=list)
    memory: List[MemoryPoint] = field(default_factory=list)
    flame: Optional[FlameNode] = None

    # tables
    top_funcs: List[Dict[str, Any]] = field(default_factory=list)  # from pstats
    call_edges: List[HotPathEdge] = field(default_factory=list)
    suggestions: List[Suggestion] = field(default_factory=list)
    bookmarks: List[Bookmark] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        def f_to(d: StackFrame) -> Dict[str, Any]:
            return {"function": d.function, "filename": d.filename, "lineno": d.lineno}

        def flame_to(n: FlameNode) -> Dict[str, Any]:
            return {
                "name": n.name,
                "value": n.value,
                "self_value": n.self_value,
                "frame": f_to(n.frame) if n.frame else None,
                "children": {k: flame_to(v) for k, v in n.children.items()},
            }

        return {
            "session_id": self.session_id,
            "name": self.name,
            "created_at": self.created_at,
            "meta": self.meta,
            "samples": [
                {"t": s.t, "dt": s.dt, "category": s.category, "stack": [f_to(fr) for fr in s.stack]}
                for s in self.samples
            ],
            "spans": [
                {
                    "span_id": sp.span_id,
                    "name": sp.name,
                    "start": sp.start,
                    "end": sp.end,
                    "category": sp.category,
                    "depth": sp.depth,
                    "meta": sp.meta,
                }
                for sp in self.spans
            ],
            "memory": [
                {"t": m.t, "current": m.current, "peak": m.peak, "top": m.top, "label": m.label}
                for m in self.memory
            ],
            "flame": flame_to(self.flame) if self.flame else None,
            "top_funcs": self.top_funcs,
            "call_edges": [{"src": e.src, "dst": e.dst, "weight": e.weight} for e in self.call_edges],
            "suggestions": [
                {
                    "severity": s.severity,
                    "title": s.title,
                    "description": s.description,
                    "evidence": s.evidence,
                    "action": s.action,
                    "focus_link": s.focus_link,
                    "category": s.category,
                }
                for s in self.suggestions
            ],
            "bookmarks": [{"name": b.name, "link": b.link, "note": b.note, "created_at": b.created_at} for b in self.bookmarks],
        }

    def to_json(self) -> str:
        return _stable_json_dumps(self.to_dict())

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "ProfileSession":
        def f_from(x: Dict[str, Any]) -> StackFrame:
            return StackFrame(function=x["function"], filename=x["filename"], lineno=int(x["lineno"]))

        def flame_from(x: Dict[str, Any]) -> FlameNode:
            n = FlameNode(
                name=x["name"],
                value=float(x.get("value", 0.0)),
                self_value=float(x.get("self_value", 0.0)),
                frame=f_from(x["frame"]) if x.get("frame") else None,
            )
            kids = x.get("children", {}) or {}
            for k, v in kids.items():
                n.children[k] = flame_from(v)
            return n

        s = cls(
            session_id=d["session_id"],
            name=d["name"],
            created_at=float(d["created_at"]),
            meta=d.get("meta", {}) or {},
        )
        s.samples = [
            ProfileSample(
                t=float(x["t"]),
                dt=float(x["dt"]),
                category=x.get("category", "cpu"),
                stack=[f_from(fr) for fr in x.get("stack", [])],
            )
            for x in d.get("samples", [])
        ]
        s.spans = [
            TimelineSpan(
                span_id=x["span_id"],
                name=x["name"],
                start=float(x["start"]),
                end=float(x["end"]),
                category=x.get("category", "cpu"),
                depth=int(x.get("depth", 0)),
                meta=x.get("meta", {}) or {},
            )
            for x in d.get("spans", [])
        ]
        s.memory = [
            MemoryPoint(t=float(x["t"]), current=int(x["current"]), peak=int(x["peak"]), top=x.get("top", []) or [], label=x.get("label", ""))
            for x in d.get("memory", [])
        ]
        s.flame = flame_from(d["flame"]) if d.get("flame") else None
        s.top_funcs = d.get("top_funcs", []) or []
        s.call_edges = [HotPathEdge(src=e["src"], dst=e["dst"], weight=float(e["weight"])) for e in d.get("call_edges", [])]
        s.suggestions = [
            Suggestion(
                severity=x["severity"],
                title=x["title"],
                description=x["description"],
                evidence=x["evidence"],
                action=x["action"],
                focus_link=x.get("focus_link", ""),
                category=x.get("category", "general"),
            )
            for x in d.get("suggestions", [])
        ]
        s.bookmarks = [Bookmark(name=b["name"], link=b["link"], note=b.get("note", ""), created_at=float(b.get("created_at", time.time()))) for b in d.get("bookmarks", [])]
        return s

    @classmethod
    def from_json(cls, s: str) -> "ProfileSession":
        return cls.from_dict(json.loads(s))


# -------------------------- Link / Focus --------------------------

class Linker:
    """Creates and parses shareable perflens:// links."""
    @staticmethod
    def focus_link(kind: str, **params: Any) -> str:
        # perflens://focus?kind=flame&name=... etc.
        q = {"kind": kind}
        for k, v in params.items():
            q[k] = str(v)
        return f"perflens://focus?{urlencode(q, doseq=True)}"

    @staticmethod
    def parse(link: str) -> Optional[Dict[str, str]]:
        try:
            u = urlparse(link.strip())
            if u.scheme != "perflens" or u.netloc != "focus":
                return None
            qs = parse_qs(u.query)
            out: Dict[str, str] = {}
            for k, v in qs.items():
                out[k] = v[0] if v else ""
            return out
        except Exception:
            return None


# -------------------------- Virtualized Models --------------------------

class TopFuncsModel(QAbstractTableModel):
    COLS = ["Function", "Cum", "Self", "Calls", "Location"]

    def __init__(self) -> None:
        super().__init__()
        self.rows: List[Dict[str, Any]] = []
        self.filter_text = ""

    def set_rows(self, rows: List[Dict[str, Any]]) -> None:
        self.beginResetModel()
        self.rows = rows
        self.endResetModel()

    def set_filter(self, t: str) -> None:
        self.filter_text = (t or "").lower()
        self.layoutChanged.emit()

    def _visible(self) -> List[Dict[str, Any]]:
        if not self.filter_text:
            return self.rows
        ft = self.filter_text
        out = []
        for r in self.rows:
            hay = f"{r.get('func','')} {r.get('file','')}:{r.get('line','')}".lower()
            if ft in hay:
                out.append(r)
        return out

    def rowCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return len(self._visible())

    def columnCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return len(self.COLS)

    def headerData(self, section: int, orientation: Qt.Orientation, role: int = Qt.DisplayRole) -> Any:
        if orientation == Qt.Horizontal and role == Qt.DisplayRole:
            return self.COLS[section]
        return None

    def data(self, index: QModelIndex, role: int = Qt.DisplayRole) -> Any:
        if not index.isValid():
            return None
        rows = self._visible()
        if index.row() >= len(rows):
            return None
        r = rows[index.row()]
        col = index.column()

        if role == Qt.DisplayRole:
            if col == 0:
                return r.get("func", "")
            if col == 1:
                return _human_ms(float(r.get("cum", 0.0)))
            if col == 2:
                return _human_ms(float(r.get("self", 0.0)))
            if col == 3:
                return str(r.get("calls", 0))
            if col == 4:
                return f"{_short_file(r.get('file',''))}:{r.get('line',0)}"
        if role == Qt.ToolTipRole:
            return f"{r.get('func','')}\n{r.get('file','')}:{r.get('line',0)}\nCum {_human_ms(float(r.get('cum',0.0)))} | Self {_human_ms(float(r.get('self',0.0)))} | Calls {r.get('calls',0)}"
        if role == Qt.UserRole:
            return r
        return None


class SuggestionsModel(QAbstractTableModel):
    COLS = ["Severity", "Category", "Issue", "Action"]

    def __init__(self) -> None:
        super().__init__()
        self.rows: List[Suggestion] = []
        self.filter_text = ""

    def set_rows(self, rows: List[Suggestion]) -> None:
        self.beginResetModel()
        self.rows = rows
        self.endResetModel()

    def set_filter(self, t: str) -> None:
        self.filter_text = (t or "").lower()
        self.layoutChanged.emit()

    def _visible(self) -> List[Suggestion]:
        if not self.filter_text:
            return self.rows
        ft = self.filter_text
        return [s for s in self.rows if ft in (s.title + " " + s.description + " " + s.category).lower()]

    def rowCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return len(self._visible())

    def columnCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return len(self.COLS)

    def headerData(self, section: int, orientation: Qt.Orientation, role: int = Qt.DisplayRole) -> Any:
        if orientation == Qt.Horizontal and role == Qt.DisplayRole:
            return self.COLS[section]
        return None

    def data(self, index: QModelIndex, role: int = Qt.DisplayRole) -> Any:
        if not index.isValid():
            return None
        rows = self._visible()
        if index.row() >= len(rows):
            return None
        s = rows[index.row()]
        col = index.column()

        if role == Qt.DisplayRole:
            if col == 0:
                return s.severity.upper()
            if col == 1:
                return s.category
            if col == 2:
                return s.title
            if col == 3:
                return s.action
        if role == Qt.ToolTipRole:
            return f"{s.description}\n\nEvidence:\n{s.evidence}\n\nJump: {s.focus_link or '—'}"
        if role == Qt.ForegroundRole and col == 0:
            if s.severity == "critical":
                return _qcolor(DARK["bad"])
            if s.severity == "warning":
                return _qcolor(DARK["warn"])
            return _qcolor(DARK["good"])
        if role == Qt.UserRole:
            return s
        return None


# -------------------------- Render Throttling / Quality --------------------------

class RenderThrottle:
    """Coalesce frequent update() calls into ~60Hz (or lower) to keep UI snappy."""
    def __init__(self, widget: QWidget, hz: int = 60) -> None:
        self.widget = widget
        self.timer = QTimer(widget)
        self.timer.setSingleShot(True)
        self.timer.timeout.connect(widget.update)
        self.interval_ms = max(8, int(1000 / max(10, hz)))

    def poke(self) -> None:
        if not self.timer.isActive():
            self.timer.start(self.interval_ms)


# -------------------------- Flame Graph (Sampling) --------------------------

class FlameGraphWidget(QWidget):
    nodeClicked = Signal(str)  # path_key
    nodeHovered = Signal(str)

    def __init__(self, theme: Dict[str, str]) -> None:
        super().__init__()
        self.theme = theme
        self.setMouseTracking(True)
        self.setMinimumHeight(250)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

        self.root: Optional[FlameNode] = None
        self.compare_root: Optional[FlameNode] = None
        self.diff_mode = False

        self.search = ""
        self.selected_path: str = ""
        self.hover_path: str = ""

        self.zoom = 1.0
        self.pan = QPointF(0, 0)

        self.row_h = 24
        self.min_w = 2.0

        self._layout: List[Tuple[str, QRectF, FlameNode, int]] = []
        self._layout_dirty = True

        self._fps_last = time.perf_counter()
        self._fps_counter = 0
        self._fps = 60.0
        self._quality = 1.0

        self.throttle = RenderThrottle(self, hz=60)

        self._drag_mid = False
        self._drag_start = QPointF(0, 0)
        self._pan_start = QPointF(0, 0)

    def setTheme(self, theme: Dict[str, str]) -> None:
        self.theme = theme
        self.throttle.poke()

    def setData(self, root: Optional[FlameNode]) -> None:
        self.root = root
        self._layout_dirty = True
        self.zoom = 1.0
        self.pan = QPointF(0, 0)
        self.selected_path = ""
        self.hover_path = ""
        self.throttle.poke()

    def setCompare(self, root: Optional[FlameNode]) -> None:
        self.compare_root = root
        self.diff_mode = root is not None
        self.throttle.poke()

    def setSearch(self, text: str) -> None:
        self.search = (text or "").lower()
        self.throttle.poke()

    def resetView(self) -> None:
        self.zoom = 1.0
        self.pan = QPointF(0, 0)
        self.selected_path = ""
        self.throttle.poke()

    def zoomIn(self) -> None:
        self.zoom = min(6.0, self.zoom * 1.18)
        self._layout_dirty = True
        self.throttle.poke()

    def zoomOut(self) -> None:
        self.zoom = max(0.6, self.zoom / 1.18)
        self._layout_dirty = True
        self.throttle.poke()

    def focusPath(self, path_key: str) -> None:
        if not path_key:
            return
        for k, rect, _, _ in self._layout:
            if k == path_key:
                self.selected_path = k
                target = rect.center()
                self.pan = QPointF(self.width() / 2 - target.x(), self.height() / 2 - target.y())
                self.throttle.poke()
                return

    def _compute_layout(self) -> None:
        self._layout = []
        if not self.root:
            self._layout_dirty = False
            return

        maxw = max(1, self.width()) * self.zoom
        total = max(1e-9, self.root.value)

        # quality control: if fps drops, increase min_w and reduce label density
        # (quality in [0.4..1.2])
        q = self._quality
        min_w = self.min_w * (2.0 - q)  # lower q => larger min_w
        min_w = max(2.0, min(12.0, min_w))

        def place(node: FlameNode, x: float, y: float, w: float, depth: int, path: Tuple[str, ...]) -> None:
            if w < min_w:
                return
            key = " / ".join(path + (node.name,))
            rect = QRectF(x, y, w, self.row_h - 3)
            self._layout.append((key, rect, node, depth))

            if not node.children:
                return
            # children widths proportional to node.value (not root)
            base = max(1e-9, node.value)
            cx = x
            for _, child in sorted(node.children.items(), key=lambda kv: kv[1].value, reverse=True):
                cw = w * (child.value / base)
                if cw >= min_w:
                    place(child, cx, y + self.row_h, cw, depth + 1, path + (node.name,))
                    cx += cw

        place(self.root, 0.0, 0.0, maxw, 0, tuple())
        self._layout_dirty = False

    def _path_map(self, root: Optional[FlameNode]) -> Dict[str, FlameNode]:
        if not root:
            return {}
        out: Dict[str, FlameNode] = {}
        for path, node in root.iter_nodes(()):
            out[" / ".join(path)] = node
        return out

    def _diff_color(self, key: str, node: FlameNode) -> QColor:
        # compare by path key (stable within run)
        base = _qcolor(self.theme["flame_warm"])
        if not self.compare_root:
            return base
        a = node.value
        mp = self._path_map(self.compare_root)
        bnode = mp.get(key)
        if not bnode:
            return _qcolor(self.theme["accent"])
        b = bnode.value
        if b <= 1e-9:
            return _qcolor(self.theme["bad"])
        ratio = a / b
        if ratio > 1.12:
            # red for regression
            t = min(1.0, (ratio - 1.0) / 0.8)
            return _blend(_qcolor(self.theme["flame_warm"]), _qcolor(self.theme["bad"]), t)
        if ratio < 0.88:
            t = min(1.0, (1.0 - ratio) / 0.8)
            return _blend(_qcolor(self.theme["flame_warm"]), _qcolor(self.theme["good"]), t)
        return base

    def _heat_color(self, node: FlameNode) -> QColor:
        if node.value <= 1e-9:
            return _qcolor(self.theme["flame_cold"])
        r = node.self_value / max(1e-9, node.value)
        cold = _qcolor(self.theme["flame_cold"])
        warm = _qcolor(self.theme["flame_warm"])
        hot = _qcolor(self.theme["flame_hot"])
        if r < 0.5:
            return _blend(cold, warm, r * 2)
        return _blend(warm, hot, (r - 0.5) * 2)

    def paintEvent(self, e) -> None:
        t0 = time.perf_counter()
        if self._layout_dirty:
            self._compute_layout()

        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing, True)
        p.fillRect(self.rect(), _qcolor(self.theme["panel2"]))

        if not self.root:
            p.setPen(_qcolor(self.theme["muted"]))
            p.setFont(QFont("Segoe UI", 10))
            p.drawText(self.rect(), Qt.AlignCenter, "No flame graph yet")
            return

        p.translate(self.pan)

        font = QFont("Segoe UI", 9)
        p.setFont(font)
        fm = QFontMetrics(font)

        # slight gradient background grid
        p.setPen(QPen(_qcolor(self.theme["grid"]), 1))
        for y in range(0, int((self.height() - self.pan.y()) / self.row_h) + 3):
            yy = y * self.row_h
            p.drawLine(0, yy, int(self.width() * self.zoom), yy)

        for key, rect, node, depth in self._layout:
            # cull
            if rect.right() + self.pan.x() < -40 or rect.left() + self.pan.x() > self.width() + 40:
                continue
            if rect.bottom() + self.pan.y() < -40 or rect.top() + self.pan.y() > self.height() + 40:
                continue

            # color
            if self.diff_mode:
                c = self._diff_color(key, node)
            else:
                c = self._heat_color(node)

            # highlight search
            if self.search and self.search in node.name.lower():
                c = _blend(c, _qcolor(self.theme["accent"]), 0.5)

            p.setPen(QPen(_qcolor(self.theme["stroke"]), 1))
            p.setBrush(c)
            radius = 4.0
            p.drawRoundedRect(rect, radius, radius)

            # selection / hover outlines
            if key == self.selected_path:
                p.setPen(QPen(_qcolor(self.theme["accent2"]), 2))
                p.setBrush(Qt.NoBrush)
                p.drawRoundedRect(rect.adjusted(1.0, 1.0, -1.0, -1.0), radius, radius)
            elif key == self.hover_path:
                p.setPen(QPen(_qcolor(self.theme["accent"]), 2))
                p.setBrush(Qt.NoBrush)
                p.drawRoundedRect(rect.adjusted(1.0, 1.0, -1.0, -1.0), radius, radius)

            # label
            if rect.width() >= 55:
                label = node.name
                maxw = rect.width() - 10
                if fm.horizontalAdvance(label) > maxw:
                    # elide
                    ell = "…"
                    while label and fm.horizontalAdvance(label + ell) > maxw:
                        label = label[:-1]
                    label = (label + ell) if label else ell
                p.setPen(_qcolor(self.theme["text"]))
                p.drawText(rect.adjusted(6, 0, -6, 0), Qt.AlignVCenter | Qt.AlignLeft, label)

        # HUD
        p.resetTransform()
        chip = QRectF(10, 10, 260, 26)
        p.setPen(Qt.NoPen)
        p.setBrush(_qcolor(self.theme["chip"]))
        p.drawRoundedRect(chip, 10, 10)
        p.setPen(_qcolor(self.theme["muted"]))
        p.setFont(QFont("Segoe UI", 9))
        info = f"Flame Graph • sampling stacks • zoom {self.zoom:.2f}x"
        if self.diff_mode:
            info += " • DIFF"
        p.drawText(chip.adjusted(10, 0, -10, 0), Qt.AlignVCenter | Qt.AlignLeft, info)

        # fps
        self._fps_counter += 1
        if self._fps_counter >= 20:
            now = time.perf_counter()
            dt = max(1e-6, now - self._fps_last)
            self._fps = self._fps_counter / dt
            self._fps_last = now
            self._fps_counter = 0
            # quality adjust
            if self._fps < 28:
                self._quality = max(0.45, self._quality * 0.92)
                self._layout_dirty = True
            elif self._fps > 55:
                self._quality = min(1.15, self._quality * 1.03)
                self._layout_dirty = True

        # paint cost dims quality slightly if too slow
        cost = time.perf_counter() - t0
        if cost > 0.03:
            self._quality = max(0.45, self._quality * 0.98)

    def _hit(self, pos: QPointF) -> Optional[Tuple[str, QRectF, FlameNode]]:
        x = pos.x() - self.pan.x()
        y = pos.y() - self.pan.y()
        pt = QPointF(x, y)
        # iterate reverse for topmost depth
        for key, rect, node, _ in reversed(self._layout):
            if rect.contains(pt):
                return key, rect, node
        return None

    def mouseMoveEvent(self, e) -> None:
        hit = self._hit(e.position())
        if hit:
            key, rect, node = hit
            self.hover_path = key
            self.setCursor(Qt.PointingHandCursor)
            self.nodeHovered.emit(key)
            tip = (
                f"<b>{node.name}</b><br>"
                f"Total: {_human_ms(node.value)}<br>"
                f"Self: {_human_ms(node.self_value)}"
            )
            if node.frame:
                tip += f"<br><span style='color:{self.theme['muted']}'>@ {_short_file(node.frame.filename)}:{node.frame.lineno}</span>"
            if self.diff_mode and self.compare_root:
                mp = self._path_map(self.compare_root)
                bn = mp.get(key)
                if bn:
                    delta = node.value - bn.value
                    sign = "+" if delta >= 0 else ""
                    tip += f"<br><b>Δ</b> {sign}{_human_ms(delta)} (A/B: {node.value/max(1e-9,bn.value):.2f}×)"
            self.setToolTip(tip)
        else:
            self.hover_path = ""
            self.setCursor(Qt.ArrowCursor)
            self.setToolTip("")
        self.throttle.poke()

        if self._drag_mid:
            delta = e.position() - self._drag_start
            self.pan = self._pan_start + delta
            self.throttle.poke()

    def mousePressEvent(self, e) -> None:
        if e.button() == Qt.LeftButton:
            hit = self._hit(e.position())
            if hit:
                key, _, _ = hit
                self.selected_path = key
                self.nodeClicked.emit(key)
                self.throttle.poke()
        elif e.button() == Qt.MiddleButton:
            self._drag_mid = True
            self._drag_start = e.position()
            self._pan_start = self.pan
            self.setCursor(Qt.ClosedHandCursor)

    def mouseReleaseEvent(self, e) -> None:
        if e.button() == Qt.MiddleButton and self._drag_mid:
            self._drag_mid = False
            self.setCursor(Qt.ArrowCursor)

    def wheelEvent(self, e) -> None:
        if e.angleDelta().y() > 0:
            self.zoomIn()
        else:
            self.zoomOut()

    def resizeEvent(self, e) -> None:
        self._layout_dirty = True
        self.throttle.poke()
        super().resizeEvent(e)


# -------------------------- Timeline --------------------------

class TimelineWidget(QWidget):
    spanClicked = Signal(str)  # span_id
    spanHovered = Signal(str)
    rangeChanged = Signal(float, float)

    def __init__(self, theme: Dict[str, str]) -> None:
        super().__init__()
        self.theme = theme
        self.setMouseTracking(True)
        self.setMinimumHeight(240)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.throttle = RenderThrottle(self, hz=60)

        self.spans_all: List[TimelineSpan] = []
        self.spans: List[TimelineSpan] = []
        self.search = ""
        self.selected = ""
        self.hovered = ""

        self.view_start = 0.0
        self.view_end = 1.0

        self.row_h = 28
        self.header_h = 34
        self._rows: Dict[str, int] = {}
        self._brush: Optional[Tuple[float, float]] = None

        self._fps_last = time.perf_counter()
        self._fps_counter = 0
        self._fps = 60.0
        self._quality = 1.0  # controls max spans drawn

        self._cat_colors = {
            "cpu": "#7c5cff",
            "json": "#ff7a90",
            "db": "#fbbf24",
            "io": "#23d5ab",
            "compute": "#60a5fa",
            "memory": "#a78bfa",
            "python": "#93c5fd",
        }

    def setTheme(self, theme: Dict[str, str]) -> None:
        self.theme = theme
        self.throttle.poke()

    def setSearch(self, t: str) -> None:
        self.search = (t or "").lower()
        self._apply_filter()
        self.throttle.poke()

    def setData(self, spans: List[TimelineSpan]) -> None:
        self.spans_all = spans[:]
        self._apply_filter()
        self._auto_range()
        self._assign_rows()
        self.selected = ""
        self.hovered = ""
        self.throttle.poke()

    def _apply_filter(self) -> None:
        if not self.search:
            self.spans = list(self.spans_all)
            return
        ft = self.search
        self.spans = [s for s in self.spans_all if ft in (s.name + " " + s.category).lower()]

    def _auto_range(self) -> None:
        if not self.spans_all:
            self.view_start, self.view_end = 0.0, 1.0
            return
        self.view_start = min(s.start for s in self.spans_all)
        self.view_end = max(s.end for s in self.spans_all)
        if self.view_end <= self.view_start:
            self.view_end = self.view_start + 1.0

    def resetZoom(self) -> None:
        self._auto_range()
        self.rangeChanged.emit(self.view_start, self.view_end)
        self.throttle.poke()

    def zoomTo(self, a: float, b: float) -> None:
        a, b = float(a), float(b)
        if b <= a:
            return
        self.view_start, self.view_end = a, b
        self.rangeChanged.emit(self.view_start, self.view_end)
        self.throttle.poke()

    def focusSpan(self, span_id: str) -> None:
        if not span_id:
            return
        for s in self.spans_all:
            if s.span_id == span_id:
                self.selected = span_id
                # zoom slightly around it
                pad = max(0.002, s.dur * 0.6)
                self.zoomTo(max(0.0, s.start - pad), s.end + pad)
                return

    def _assign_rows(self) -> None:
        self._rows.clear()
        # simple interval scheduling per category to avoid overlaps
        by_cat: Dict[str, List[TimelineSpan]] = {}
        for s in self.spans:
            by_cat.setdefault(s.category, []).append(s)
        row_base = 0
        for cat in sorted(by_cat.keys()):
            ss = sorted(by_cat[cat], key=lambda x: (x.start, -x.dur))
            row_ends: List[float] = []
            for sp in ss:
                placed = False
                for i in range(len(row_ends)):
                    if row_ends[i] <= sp.start:
                        self._rows[sp.span_id] = row_base + i
                        row_ends[i] = sp.end
                        placed = True
                        break
                if not placed:
                    self._rows[sp.span_id] = row_base + len(row_ends)
                    row_ends.append(sp.end)
            row_base += max(1, len(row_ends))

    def _t_to_x(self, t: float) -> float:
        if self.view_end <= self.view_start:
            return 0.0
        return (t - self.view_start) / (self.view_end - self.view_start) * self.width()

    def _x_to_t(self, x: float) -> float:
        if self.width() <= 1:
            return self.view_start
        return self.view_start + (x / self.width()) * (self.view_end - self.view_start)

    def _span_rect(self, s: TimelineSpan) -> Tuple[QRectF, int]:
        row = self._rows.get(s.span_id, 0)
        x1 = self._t_to_x(s.start)
        x2 = self._t_to_x(s.end)
        w = max(4.0, x2 - x1)
        y = self.header_h + row * self.row_h + 4
        return QRectF(x1, y, w, self.row_h - 8), row

    def _draw_grid(self, p: QPainter) -> None:
        p.setPen(QPen(_qcolor(self.theme["grid"]), 1))
        # vertical grid lines
        rng = self.view_end - self.view_start
        if rng <= 0:
            return
        target = 9
        step = rng / target
        # round to nice ms
        mag = 10 ** int(f"{step:.0e}".split("e")[1])
        nice = max(1e-9, round(step / mag) * mag)
        start = (self.view_start // nice) * nice
        t = start
        while t <= self.view_end + nice:
            x = self._t_to_x(t)
            p.drawLine(int(x), self.header_h, int(x), self.height())
            t += nice

    def paintEvent(self, e) -> None:
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing, True)
        p.fillRect(self.rect(), _qcolor(self.theme["panel2"]))

        # header
        p.setPen(Qt.NoPen)
        p.setBrush(_qcolor(self.theme["panel"]))
        p.drawRect(0, 0, self.width(), self.header_h)
        p.setPen(_qcolor(self.theme["muted"]))
        p.setFont(QFont("Segoe UI", 9))
        p.drawText(12, 22, "Timeline • spans over time • drag to brush/zoom • double-click to reset")

        if not self.spans:
            p.setPen(_qcolor(self.theme["muted"]))
            p.setFont(QFont("Segoe UI", 10))
            p.drawText(self.rect().adjusted(0, self.header_h, 0, 0), Qt.AlignCenter, "No timeline spans yet")
            return

        self._draw_grid(p)

        # draw spans with quality cap
        # if fps low, cap to fewer spans (largest first)
        cap = int(1800 * self._quality)
        if cap < len(self.spans):
            spans = sorted(self.spans, key=lambda s: s.dur, reverse=True)[:cap]
        else:
            spans = self.spans

        p.setFont(QFont("Segoe UI", 8))
        fm = QFontMetrics(p.font())

        for s in spans:
            rect, _ = self._span_rect(s)
            if rect.right() < -40 or rect.left() > self.width() + 40:
                continue
            # color
            c = _qcolor(self._cat_colors.get(s.category, self.theme["accent"]))
            if self.search and self.search in s.name.lower():
                c = _blend(c, _qcolor(self.theme["accent"]), 0.35)

            p.setBrush(c)
            p.setPen(QPen(_qcolor(self.theme["stroke"]), 1))
            p.drawRoundedRect(rect, 5, 5)

            if s.span_id == self.selected:
                p.setPen(QPen(_qcolor(self.theme["accent2"]), 2))
                p.setBrush(Qt.NoBrush)
                p.drawRoundedRect(rect.adjusted(1, 1, -1, -1), 5, 5)
            elif s.span_id == self.hovered:
                p.setPen(QPen(_qcolor(self.theme["accent"]), 2))
                p.setBrush(Qt.NoBrush)
                p.drawRoundedRect(rect.adjusted(1, 1, -1, -1), 5, 5)

            # label
            if rect.width() > 70 and self._quality > 0.55:
                label = s.name
                maxw = rect.width() - 10
                if fm.horizontalAdvance(label) > maxw:
                    ell = "…"
                    while label and fm.horizontalAdvance(label + ell) > maxw:
                        label = label[:-1]
                    label = (label + ell) if label else ell
                p.setPen(_qcolor(self.theme["text"]))
                p.drawText(rect.adjusted(7, 0, -7, 0), Qt.AlignVCenter | Qt.AlignLeft, label)

        # brush selection overlay
        if self._brush:
            a, b = self._brush
            x1 = self._t_to_x(min(a, b))
            x2 = self._t_to_x(max(a, b))
            p.setPen(Qt.NoPen)
            overlay = _qcolor(self.theme["accent"])
            overlay.setAlpha(60)
            p.setBrush(overlay)
            p.drawRect(QRectF(x1, self.header_h, x2 - x1, self.height() - self.header_h))

        # fps / quality adjust
        self._fps_counter += 1
        if self._fps_counter >= 20:
            now = time.perf_counter()
            dt = max(1e-6, now - self._fps_last)
            self._fps = self._fps_counter / dt
            self._fps_last = now
            self._fps_counter = 0
            if self._fps < 28:
                self._quality = max(0.45, self._quality * 0.92)
            elif self._fps > 55:
                self._quality = min(1.15, self._quality * 1.03)

    def _hit(self, pos: QPointF) -> Optional[TimelineSpan]:
        for s in reversed(self.spans):
            rect, _ = self._span_rect(s)
            if rect.contains(pos):
                return s
        return None

    def mouseMoveEvent(self, e) -> None:
        if self._brush:
            a, _ = self._brush
            self._brush = (a, self._x_to_t(e.position().x()))
            self.throttle.poke()
            return

        hit = self._hit(e.position())
        if hit:
            self.hovered = hit.span_id
            self.spanHovered.emit(hit.span_id)
            self.setCursor(Qt.PointingHandCursor)
            tip = (
                f"<b>{hit.name}</b><br>"
                f"Category: {hit.category}<br>"
                f"Duration: {_human_ms(hit.dur)}<br>"
                f"Start: {_human_ms(hit.start)}"
            )
            if hit.meta:
                for k, v in list(hit.meta.items())[:6]:
                    tip += f"<br><span style='color:{self.theme['muted']}'>{k}: {v}</span>"
            self.setToolTip(tip)
        else:
            self.hovered = ""
            self.setCursor(Qt.ArrowCursor)
            self.setToolTip("")
        self.throttle.poke()

    def mousePressEvent(self, e) -> None:
        if e.button() == Qt.LeftButton:
            hit = self._hit(e.position())
            if hit:
                self.selected = hit.span_id
                self.spanClicked.emit(hit.span_id)
                self.throttle.poke()
            else:
                # start brush
                t = self._x_to_t(e.position().x())
                self._brush = (t, t)
                self.throttle.poke()

    def mouseReleaseEvent(self, e) -> None:
        if e.button() == Qt.LeftButton and self._brush:
            a, b = self._brush
            self._brush = None
            if abs(b - a) > 0.002:
                self.zoomTo(min(a, b), max(a, b))
            self.throttle.poke()

    def mouseDoubleClickEvent(self, e) -> None:
        self.resetZoom()

    def wheelEvent(self, e) -> None:
        # zoom around cursor
        cur = self._x_to_t(e.position().x())
        rng = self.view_end - self.view_start
        if rng <= 1e-9:
            return
        factor = 0.8 if e.angleDelta().y() > 0 else 1.25
        new_rng = max(0.002, rng * factor)
        frac = 0.0
        if rng > 0:
            frac = (cur - self.view_start) / rng
        a = cur - new_rng * frac
        b = a + new_rng
        self.zoomTo(a, b)


# -------------------------- Memory Heatmap --------------------------

class MemoryHeatmapWidget(QWidget):
    pointClicked = Signal(int)  # index

    def __init__(self, theme: Dict[str, str]) -> None:
        super().__init__()
        self.theme = theme
        self.setMouseTracking(True)
        self.setMinimumHeight(200)
        self.points: List[MemoryPoint] = []
        self.hover: Optional[Tuple[int, int]] = None  # (col,row)
        self.cell = 18
        self.throttle = RenderThrottle(self, hz=60)

    def setTheme(self, theme: Dict[str, str]) -> None:
        self.theme = theme
        self.throttle.poke()

    def setData(self, points: List[MemoryPoint]) -> None:
        self.points = points[:]
        self.hover = None
        self.throttle.poke()

    def paintEvent(self, e) -> None:
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing, True)
        p.fillRect(self.rect(), _qcolor(self.theme["panel2"]))

        p.setFont(QFont("Segoe UI", 9))
        p.setPen(_qcolor(self.theme["muted"]))
        p.drawText(12, 22, "Memory • tracemalloc checkpoints • heatmap of top alloc sites (size, by time)")

        if not self.points:
            p.setPen(_qcolor(self.theme["muted"]))
            p.setFont(QFont("Segoe UI", 10))
            p.drawText(self.rect().adjusted(0, 30, 0, 0), Qt.AlignCenter, "No memory checkpoints yet")
            return

        cols = min(len(self.points), max(1, int((self.width() - 20) / self.cell)))
        # rows based on top alloc sites
        rows = 0
        for pt in self.points[:cols]:
            rows = max(rows, len(pt.top))
        rows = min(rows, max(1, int((self.height() - 80) / self.cell)))

        # peak for line
        peak = max(pt.peak for pt in self.points) if self.points else 1

        # max site size for heat intensity
        max_site = 1
        for pt in self.points[:cols]:
            for s in pt.top[:rows]:
                max_site = max(max_site, int(s.get("size", 0)))

        # legend chips
        def chip(x: int, y: int, label: str, color: str) -> None:
            p.setPen(Qt.NoPen)
            p.setBrush(_qcolor(color))
            p.drawRoundedRect(x, y, 12, 12, 4, 4)
            p.setPen(_qcolor(self.theme["muted"]))
            p.drawText(x + 16, y + 11, label)

        chip(self.width() - 170, 10, "Low", self.theme["good"])
        chip(self.width() - 110, 10, "Mid", self.theme["warn"])
        chip(self.width() - 50, 10, "High", self.theme["bad"])

        base_x = 12
        base_y = 42

        for c in range(cols):
            pt = self.points[c]
            for r in range(min(rows, len(pt.top))):
                site = pt.top[r]
                size = int(site.get("size", 0))
                intensity = size / max_site
                if intensity < 0.33:
                    col = _qcolor(self.theme["good"])
                elif intensity < 0.66:
                    col = _qcolor(self.theme["warn"])
                else:
                    col = _qcolor(self.theme["bad"])
                rect = QRectF(base_x + c * self.cell, base_y + r * self.cell, self.cell - 2, self.cell - 2)
                p.setPen(Qt.NoPen)
                p.setBrush(col)
                p.drawRoundedRect(rect, 4, 4)
                if self.hover == (c, r):
                    p.setPen(QPen(_qcolor(self.theme["accent"]), 2))
                    p.setBrush(Qt.NoBrush)
                    p.drawRoundedRect(rect.adjusted(1, 1, -1, -1), 4, 4)

        # memory line chart under heatmap
        chart_top = base_y + rows * self.cell + 12
        chart_h = max(40, self.height() - chart_top - 10)
        p.setPen(QPen(_qcolor(self.theme["accent"]), 2))
        path = QPainterPath()
        for i in range(cols):
            pt = self.points[i]
            x = base_x + i * self.cell + (self.cell / 2)
            y = chart_top + (1.0 - pt.current / max(1, peak)) * (chart_h - 8) + 4
            if i == 0:
                path.moveTo(x, y)
            else:
                path.lineTo(x, y)
        p.drawPath(path)

        p.setPen(_qcolor(self.theme["muted"]))
        p.setFont(QFont("Segoe UI", 8))
        p.drawText(base_x, chart_top + chart_h - 2, f"Peak { _human_bytes(peak) }")

        # labels for columns (checkpoint names)
        for i in range(cols):
            pt = self.points[i]
            if not pt.label:
                continue
            lbl = pt.label
            if len(lbl) > 18:
                lbl = lbl[:17] + "…"
            p.save()
            p.translate(base_x + i * self.cell + 6, base_y - 4)
            p.rotate(-50)
            p.setPen(_qcolor(self.theme["muted"]))
            p.drawText(0, 0, lbl)
            p.restore()

    def mouseMoveEvent(self, e) -> None:
        if not self.points:
            return
        cols = min(len(self.points), max(1, int((self.width() - 20) / self.cell)))
        rows = 0
        for pt in self.points[:cols]:
            rows = max(rows, len(pt.top))
        rows = min(rows, max(1, int((self.height() - 80) / self.cell)))
        base_x = 12
        base_y = 42
        x = e.position().x() - base_x
        y = e.position().y() - base_y
        c = int(x // self.cell)
        r = int(y // self.cell)
        if 0 <= c < cols and 0 <= r < rows:
            pt = self.points[c]
            if r < len(pt.top):
                self.hover = (c, r)
                site = pt.top[r]
                tip = f"<b>{site.get('file','')}</b>:<b>{site.get('line','')}</b><br>Size: {_human_bytes(int(site.get('size',0)))}<br>Count: {site.get('count',0)}"
                if pt.label:
                    tip += f"<br><span style='color:{self.theme['muted']}'>Checkpoint: {pt.label}</span>"
                self.setToolTip(tip)
                self.setCursor(Qt.PointingHandCursor)
                self.throttle.poke()
                return
        self.hover = None
        self.setToolTip("")
        self.setCursor(Qt.ArrowCursor)
        self.throttle.poke()

    def mousePressEvent(self, e) -> None:
        if e.button() == Qt.LeftButton and self.hover:
            c, _ = self.hover
            self.pointClicked.emit(c)


# -------------------------- Call Graph --------------------------

class CallGraphWidget(QWidget):
    edgeClicked = Signal(str, str)  # src,dst

    def __init__(self, theme: Dict[str, str]) -> None:
        super().__init__()
        self.theme = theme
        self.setMouseTracking(True)
        self.setMinimumHeight(260)
        self.edges: List[HotPathEdge] = []
        self.nodes: List[str] = []
        self.pos: Dict[str, QPointF] = {}
        self.hover_node: str = ""
        self.hover_edge: Optional[Tuple[str, str]] = None
        self.selected_node: str = ""
        self.throttle = RenderThrottle(self, hz=60)

    def setTheme(self, theme: Dict[str, str]) -> None:
        self.theme = theme
        self.throttle.poke()

    def setData(self, edges: List[HotPathEdge]) -> None:
        self.edges = edges[:]
        self._layout()
        self.throttle.poke()

    def _layout(self) -> None:
        # collect nodes by weight
        w: Dict[str, float] = {}
        for e in self.edges:
            w[e.src] = w.get(e.src, 0.0) + e.weight
            w[e.dst] = w.get(e.dst, 0.0) + e.weight
        nodes = sorted(w.keys(), key=lambda k: w[k], reverse=True)[:20]
        self.nodes = nodes
        self.pos = {}
        if not nodes:
            return
        # radial layout stable-ish
        cx, cy = self.width() / 2, self.height() / 2 + 10
        r = min(self.width(), self.height()) * 0.32
        for i, n in enumerate(nodes):
            ang = (i / max(1, len(nodes))) * 2 * 3.1415926535
            x = cx + r * 0.92 * (0.9 * (1.0 + 0.1 * (i % 3))) * (math_cos(ang))
            y = cy + r * 0.92 * (0.9 * (1.0 + 0.1 * (i % 4))) * (math_sin(ang))
            self.pos[n] = QPointF(x, y)

    def resizeEvent(self, e) -> None:
        self._layout()
        super().resizeEvent(e)

    def paintEvent(self, e) -> None:
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing, True)
        p.fillRect(self.rect(), _qcolor(self.theme["panel2"]))
        p.setFont(QFont("Segoe UI", 9))
        p.setPen(_qcolor(self.theme["muted"]))
        p.drawText(12, 22, "Call Graph • nodes are functions • edges are “calls” inferred from stacks (weighted by time)")

        if not self.nodes:
            p.setPen(_qcolor(self.theme["muted"]))
            p.setFont(QFont("Segoe UI", 10))
            p.drawText(self.rect().adjusted(0, 30, 0, 0), Qt.AlignCenter, "No call graph yet")
            return

        # edge thickness normalization
        maxw = max((e.weight for e in self.edges), default=1e-9)
        # draw edges
        for e1 in self.edges:
            if e1.src not in self.pos or e1.dst not in self.pos:
                continue
            a = self.pos[e1.src]
            b = self.pos[e1.dst]
            t = (e1.weight / maxw)
            thick = 1.0 + t * 5.0
            col = _blend(_qcolor(self.theme["grid"]), _qcolor(self.theme["accent"]), min(1.0, 0.2 + t))
            if self.hover_edge == (e1.src, e1.dst):
                col = _qcolor(self.theme["accent2"])
                thick = max(2.0, thick + 1.5)
            p.setPen(QPen(col, thick))
            p.drawLine(a, b)
            # arrow head
            dx, dy = (b.x() - a.x()), (b.y() - a.y())
            L = (dx * dx + dy * dy) ** 0.5
            if L > 1e-6:
                ux, uy = dx / L, dy / L
                px, py = -uy, ux
                tip = QPointF(b.x() - ux * 16, b.y() - uy * 16)
                left = QPointF(tip.x() - ux * 2 + px * 6, tip.y() - uy * 2 + py * 6)
                right = QPointF(tip.x() - ux * 2 - px * 6, tip.y() - uy * 2 - py * 6)
                p.setBrush(col)
                p.setPen(Qt.NoPen)
                p.drawPolygon([b, left, right])

        # draw nodes
        p.setFont(QFont("Segoe UI", 8))
        fm = QFontMetrics(p.font())
        for n in self.nodes:
            pt = self.pos.get(n)
            if not pt:
                continue
            rad = 16
            rect = QRectF(pt.x() - rad, pt.y() - rad, rad * 2, rad * 2)
            base = _qcolor(self.theme["accent"])
            fill = _blend(base, _qcolor(self.theme["chip"]), 0.35)
            if n == self.selected_node:
                fill = _qcolor(self.theme["accent2"])
            elif n == self.hover_node:
                fill = _blend(_qcolor(self.theme["accent2"]), fill, 0.3)

            p.setPen(QPen(_qcolor(self.theme["stroke"]), 1))
            p.setBrush(fill)
            p.drawEllipse(rect)

            label = n
            if len(label) > 16:
                label = label[:15] + "…"
            tw = fm.horizontalAdvance(label)
            p.setPen(_qcolor(self.theme["text"]))
            p.drawText(int(pt.x() - tw / 2), int(pt.y() + rad + 14), label)

    def _hit_node(self, pos: QPointF) -> Optional[str]:
        for n in self.nodes:
            pt = self.pos.get(n)
            if not pt:
                continue
            if (pos - pt).manhattanLength() < 22:
                return n
        return None

    def _hit_edge(self, pos: QPointF) -> Optional[Tuple[str, str]]:
        # distance to segment test for visible edges
        best: Optional[Tuple[str, str]] = None
        best_d = 1e9
        for e in self.edges:
            if e.src not in self.pos or e.dst not in self.pos:
                continue
            a = self.pos[e.src]
            b = self.pos[e.dst]
            d = _dist_point_to_segment(pos, a, b)
            if d < best_d:
                best_d = d
                best = (e.src, e.dst)
        if best and best_d < 12.0:
            return best
        return None

    def mouseMoveEvent(self, e) -> None:
        pos = e.position()
        n = self._hit_node(pos)
        if n:
            self.hover_node = n
            self.hover_edge = None
            self.setCursor(Qt.PointingHandCursor)
            self.setToolTip(f"<b>{n}</b><br>Tip: click to focus flame graph by name")
            self.throttle.poke()
            return
        ed = self._hit_edge(pos)
        if ed:
            self.hover_edge = ed
            self.hover_node = ""
            self.setCursor(Qt.PointingHandCursor)
            self.setToolTip(f"<b>{ed[0]}</b> → <b>{ed[1]}</b><br>Tip: click to jump to call in flame graph search")
            self.throttle.poke()
            return
        self.hover_node = ""
        self.hover_edge = None
        self.setCursor(Qt.ArrowCursor)
        self.setToolTip("")
        self.throttle.poke()

    def mousePressEvent(self, e) -> None:
        if e.button() == Qt.LeftButton:
            n = self._hit_node(e.position())
            if n:
                self.selected_node = n
                self.throttle.poke()
                return
            ed = self._hit_edge(e.position())
            if ed:
                self.edgeClicked.emit(ed[0], ed[1])
                self.throttle.poke()


# -------------------------- Geometry Helpers --------------------------

def math_sin(x: float) -> float:
    # tiny sin approximation fallback? use math if available
    import math
    return math.sin(x)


def math_cos(x: float) -> float:
    import math
    return math.cos(x)


def _dist_point_to_segment(p: QPointF, a: QPointF, b: QPointF) -> float:
    # distance from p to segment ab
    ax, ay = a.x(), a.y()
    bx, by = b.x(), b.y()
    px, py = p.x(), p.y()
    dx = bx - ax
    dy = by - ay
    if dx == 0 and dy == 0:
        return ((px - ax) ** 2 + (py - ay) ** 2) ** 0.5
    t = ((px - ax) * dx + (py - ay) * dy) / (dx * dx + dy * dy)
    t = max(0.0, min(1.0, t))
    cx = ax + t * dx
    cy = ay + t * dy
    return ((px - cx) ** 2 + (py - cy) ** 2) ** 0.5


# -------------------------- Profiler Core --------------------------

class Cancelled(Exception):
    pass


class SamplingCollector:
    """Samples Python stacks by polling sys._current_frames with a timer thread."""
    def __init__(self, interval_s: float = 0.0015, max_samples: int = 200_000) -> None:
        self.interval = max(0.0008, float(interval_s))
        self.max_samples = int(max_samples)
        self.samples: List[ProfileSample] = []
        self._stop = threading.Event()
        self._thread: Optional[threading.Thread] = None
        self._start_perf = 0.0
        self._target_tid: Optional[int] = None

    def start(self, target_tid: int) -> None:
        self._target_tid = int(target_tid)
        self._start_perf = time.perf_counter()
        self._stop.clear()
        self._thread = threading.Thread(target=self._run, name="PerfLensSampler", daemon=True)
        self._thread.start()

    def stop(self) -> None:
        self._stop.set()
        if self._thread and self._thread.is_alive():
            self._thread.join(timeout=0.6)

    def _run(self) -> None:
        # measure dt between samples more accurately
        last = time.perf_counter()
        while not self._stop.is_set() and len(self.samples) < self.max_samples:
            now = time.perf_counter()
            dt = now - last
            last = now
            t_rel = now - self._start_perf
            try:
                frames = sys._current_frames()
                frm = frames.get(self._target_tid) if self._target_tid else None
                if frm is None:
                    time.sleep(self.interval)
                    continue
                stack: List[StackFrame] = []
                # walk frames
                depth = 0
                while frm and depth < 70:
                    code = frm.f_code
                    stack.append(StackFrame(function=code.co_name, filename=code.co_filename, lineno=frm.f_lineno))
                    frm = frm.f_back
                    depth += 1
                stack.reverse()
                cat = _categorize_stack(stack)
                self.samples.append(ProfileSample(t=t_rel, dt=max(dt, self.interval), stack=stack, category=cat))
            except Exception:
                # keep sampling even if frame collection fails
                pass
            time.sleep(self.interval)


def _categorize_stack(stack: List[StackFrame]) -> str:
    # heuristics: recognize common modules and demo spans
    if not stack:
        return "cpu"
    s = " ".join(fr.filename for fr in stack[-12:])
    n = " ".join(fr.function for fr in stack[-12:])
    if "sqlite3" in s or "sqlite3" in n:
        return "db"
    if "json" in s or "json" in n:
        return "json"
    if "asyncio" in s or "asyncio" in n:
        return "io"
    if "sleep" in n or "select" in n:
        return "io"
    if any("convolve" in fr.function or "pixel" in fr.function or "matrix" in fr.function for fr in stack[-12:]):
        return "compute"
    return "cpu"


class MemoryRecorder:
    """Records tracemalloc checkpoints and top allocation sites."""
    def __init__(self) -> None:
        self.points: List[MemoryPoint] = []
        self._start_perf = 0.0

    def start(self) -> None:
        import tracemalloc
        tracemalloc.start()
        self._start_perf = time.perf_counter()
        self.checkpoint("start")

    def stop(self) -> None:
        import tracemalloc
        self.checkpoint("end")
        tracemalloc.stop()

    def checkpoint(self, label: str = "") -> None:
        import tracemalloc
        try:
            snap = tracemalloc.take_snapshot()
            cur, peak = tracemalloc.get_traced_memory()
            stats = snap.statistics("lineno")
            top = []
            for st in stats[:14]:
                frame = st.traceback[0]
                top.append({"file": _short_file(frame.filename), "line": frame.lineno, "size": st.size, "count": st.count})
            t = time.perf_counter() - self._start_perf
            self.points.append(MemoryPoint(t=t, current=cur, peak=peak, top=top, label=label))
        except Exception:
            pass


class PerformanceProfiler:
    """
    Profiles a callable using:
    - cProfile/pstats to get deterministic function stats
    - sampling stacks (sys._current_frames + timer thread) for flame graph + timeline
    - tracemalloc checkpoints for memory heatmap
    Optional rerun: sys.setprofile deep trace to refine call edges.
    """

    def __init__(self) -> None:
        self.cancel_flag = threading.Event()

    def cancel(self) -> None:
        self.cancel_flag.set()

    def _maybe_cancel(self) -> None:
        if self.cancel_flag.is_set():
            raise Cancelled()

    def run_callable(
        self,
        name: str,
        fn: Callable[[], Any],
        *,
        sample_interval: float = 0.0015,
        max_samples: int = 120_000,
        memory_checkpoints: Optional[List[Tuple[float, str]]] = None,
        include_deep_trace: bool = False,
        deep_trace_budget_s: float = 1.8,
        meta: Optional[Dict[str, Any]] = None,
    ) -> ProfileSession:
        self.cancel_flag.clear()
        session_id = hashlib.md5(f"{time.time()}:{random.random()}".encode()).hexdigest()[:12]
        sess = ProfileSession(session_id=session_id, name=name, created_at=time.time(), meta=meta or {})

        # memory
        mem = MemoryRecorder()
        # sampling
        sampler = SamplingCollector(interval_s=sample_interval, max_samples=max_samples)

        prof = cProfile.Profile()
        exc: Optional[BaseException] = None

        # cancellation trace: light check every N lines
        counter = {"n": 0}

        def tracefunc(frame, event, arg):
            # check rarely (every ~300 events) to keep overhead small
            counter["n"] += 1
            if counter["n"] % 300 == 0 and self.cancel_flag.is_set():
                raise Cancelled()
            return tracefunc

        # run in this thread; sampler watches this thread id
        target_tid = threading.get_ident()
        sampler.start(target_tid)
        mem.start()
        t0 = time.perf_counter()

        # optional scheduled checkpoints (approx by wall time since start)
        next_cp = 0
        cp_list = memory_checkpoints or []
        try:
            sys.settrace(tracefunc)
            prof.enable()
            while next_cp < len(cp_list) and (time.perf_counter() - t0) >= cp_list[next_cp][0]:
                mem.checkpoint(cp_list[next_cp][1])
                next_cp += 1
            # run
            fn()
            self._maybe_cancel()
            # final scheduled checkpoints if any were missed (rare)
            while next_cp < len(cp_list):
                mem.checkpoint(cp_list[next_cp][1])
                next_cp += 1
        except Cancelled as e:
            exc = e
        except BaseException as e:
            exc = e
        finally:
            try:
                prof.disable()
            except Exception:
                pass
            try:
                sys.settrace(None)
            except Exception:
                pass

            sampler.stop()
            mem.stop()

        dur = max(1e-9, time.perf_counter() - t0)

        # attach traces
        sess.samples = sampler.samples
        sess.memory = mem.points

        # flame from samples
        sess.flame = build_flame_from_samples(sess.samples)
        # timeline from samples (coalesce)
        sess.spans = build_timeline_from_samples(sess.samples, max_spans=5000)

        # top funcs from pstats
        sess.top_funcs = stats_top_funcs(prof, limit=200)
        # call edges from sample adjacency
        sess.call_edges = call_edges_from_samples(sess.samples, max_edges=160)

        # coach
        sess.suggestions = OptimizationCoach().suggest(sess)

        sess.meta["duration_s"] = dur
        sess.meta["sample_interval_s"] = sample_interval
        sess.meta["sample_count"] = len(sess.samples)
        sess.meta["has_deep_trace"] = False
        sess.meta["target"] = sess.meta.get("target", {})
        if exc:
            sess.meta["error"] = f"{type(exc).__name__}: {exc}"
            # include a trimmed tb for shareability
            sess.meta["traceback"] = _trim_tb()
        else:
            sess.meta.pop("error", None)
            sess.meta.pop("traceback", None)

        # optional deep trace rerun (sys.setprofile) with tight budget
        if include_deep_trace and not exc:
            try:
                edges = self._deep_trace_edges(fn, budget_s=deep_trace_budget_s)
                if edges:
                    sess.call_edges = _merge_edges(sess.call_edges, edges, max_edges=220)
                    sess.meta["has_deep_trace"] = True
            except Exception:
                pass

        return sess

    def _deep_trace_edges(self, fn: Callable[[], Any], budget_s: float = 1.8) -> List[HotPathEdge]:
        """
        Rerun quickly with sys.setprofile to infer call edges (fast-ish if filtered).
        budget_s: cut off edges collection after this wall time.
        """
        self.cancel_flag.clear()
        edges: Dict[Tuple[str, str], float] = {}
        stack: List[str] = []
        started = time.perf_counter()

        allow_patterns = (
            "demo_",
            "perflens_demo",
            "sqlite3",
            "json",
            "asyncio",
        )

        def fn_name(frame: types.FrameType) -> str:
            c = frame.f_code
            return c.co_name

        def allowed(frame: types.FrameType) -> bool:
            f = frame.f_code.co_filename
            n = frame.f_code.co_name
            s = f"{f}::{n}"
            return any(p in s for p in allow_patterns) or (f and f.endswith(".py") and "site-packages" not in f)

        def prof_func(frame, event, arg):
            if self.cancel_flag.is_set():
                raise Cancelled()
            if time.perf_counter() - started > budget_s:
                raise Cancelled()
            if event == "call":
                if not allowed(frame):
                    return prof_func
                callee = fn_name(frame)
                if stack:
                    src = stack[-1]
                    edges[(src, callee)] = edges.get((src, callee), 0.0) + 1.0
                stack.append(callee)
            elif event == "return":
                if stack:
                    stack.pop()
            return prof_func

        try:
            sys.setprofile(prof_func)
            fn()
        except Cancelled:
            pass
        except Exception:
            pass
        finally:
            try:
                sys.setprofile(None)
            except Exception:
                pass

        # convert to weighted edges
        out = [HotPathEdge(src=a, dst=b, weight=w) for (a, b), w in edges.items()]
        out.sort(key=lambda e: e.weight, reverse=True)
        return out[:180]


def _trim_tb() -> str:
    tb = traceback.format_exc()
    if not tb:
        return ""
    lines = tb.strip().splitlines()
    # keep last ~35 lines
    lines = lines[-35:]
    return "\n".join(lines)


def stats_top_funcs(prof: cProfile.Profile, limit: int = 200) -> List[Dict[str, Any]]:
    s = io.StringIO()
    st = pstats.Stats(prof, stream=s)
    st.strip_dirs()
    # st.sort_stats("cumulative")  # we'll read raw to avoid loss
    out = []
    # stats dict: (filename, line, funcname) -> (cc, nc, tt, ct, callers)
    stats = st.stats
    # sort by ct (cumtime) desc
    items = sorted(stats.items(), key=lambda kv: kv[1][3], reverse=True)
    for (file, line, func), (cc, nc, tt, ct, callers) in items[:limit]:
        out.append({"func": func, "file": file, "line": line, "calls": int(nc), "self": float(tt), "cum": float(ct)})
    return out


def build_flame_from_samples(samples: List[ProfileSample]) -> FlameNode:
    root = FlameNode(name="root", value=0.0)
    # build aggregated tree by stack keys
    for sm in samples:
        dt = float(sm.dt)
        if not sm.stack:
            continue
        root.value += dt
        node = root
        for fr in sm.stack:
            key = fr.key  # stable per file/line
            node = node.child(key, fr.function, fr)
            node.value += dt
        node.self_value += dt
    # normalize: ensure parents at least sum of children (sampling can skip)
    def fix(n: FlameNode) -> float:
        s = sum(fix(c) for c in n.children.values())
        n.value = max(n.value, s, n.self_value)
        return n.value
    fix(root)
    return root


def build_timeline_from_samples(samples: List[ProfileSample], max_spans: int = 5000) -> List[TimelineSpan]:
    if not samples:
        return []
    # coalesce consecutive samples by "activity key" (leaf frame + category)
    # produce spans with approximate timing; depth is stack depth for visualization layering
    spans: List[TimelineSpan] = []
    cur_key = None
    cur_start = samples[0].t
    cur_cat = samples[0].category
    cur_name = samples[0].stack[-1].function if samples[0].stack else "<idle>"
    cur_depth = len(samples[0].stack)

    def close(end_t: float) -> None:
        nonlocal cur_key, cur_start, cur_cat, cur_name, cur_depth
        if cur_key is None:
            return
        span_id = hashlib.md5(f"{cur_key}:{cur_start}:{end_t}".encode()).hexdigest()[:10]
        spans.append(
            TimelineSpan(
                span_id=span_id,
                name=cur_name,
                start=cur_start,
                end=end_t,
                category=cur_cat,
                depth=max(0, cur_depth),
                meta={},
            )
        )

    for sm in samples:
        if not sm.stack:
            key = ("<idle>", sm.category)
            name = "<idle>"
            depth = 0
        else:
            leaf = sm.stack[-1]
            key = (leaf.key, sm.category)
            name = leaf.function
            depth = len(sm.stack)
        if cur_key is None:
            cur_key = key
            cur_start = sm.t
            cur_cat = sm.category
            cur_name = name
            cur_depth = depth
            continue
        if key != cur_key:
            close(sm.t)
            cur_key = key
            cur_start = sm.t
            cur_cat = sm.category
            cur_name = name
            cur_depth = depth

    close(samples[-1].t + samples[-1].dt)

    # merge tiny spans into neighbors to reduce noise if too many
    if len(spans) > max_spans:
        # compute threshold to shrink
        durs = sorted((sp.dur for sp in spans))
        cutoff = durs[max(0, len(durs) - max_spans)]
        merged: List[TimelineSpan] = []
        for sp in spans:
            if sp.dur < cutoff and merged:
                # merge into previous if same category
                prev = merged[-1]
                if prev.category == sp.category:
                    prev.end = sp.end
                    continue
            merged.append(sp)
        spans = merged[:max_spans]

    return spans


def call_edges_from_samples(samples: List[ProfileSample], max_edges: int = 160) -> List[HotPathEdge]:
    # infer call edges by adjacent stack frames weighted by time
    w: Dict[Tuple[str, str], float] = {}
    for sm in samples:
        st = sm.stack
        if len(st) < 2:
            continue
        dt = sm.dt
        # only use the deepest ~10 frames to avoid noise
        seg = st[-12:]
        for a, b in zip(seg, seg[1:]):
            w[(a.function, b.function)] = w.get((a.function, b.function), 0.0) + dt
    edges = [HotPathEdge(src=a, dst=b, weight=x) for (a, b), x in w.items()]
    edges.sort(key=lambda e: e.weight, reverse=True)
    return edges[:max_edges]


def _merge_edges(a: List[HotPathEdge], b: List[HotPathEdge], max_edges: int = 220) -> List[HotPathEdge]:
    m: Dict[Tuple[str, str], float] = {}
    for e in a:
        m[(e.src, e.dst)] = m.get((e.src, e.dst), 0.0) + e.weight
    for e in b:
        m[(e.src, e.dst)] = m.get((e.src, e.dst), 0.0) + e.weight
    out = [HotPathEdge(src=k[0], dst=k[1], weight=v) for k, v in m.items()]
    out.sort(key=lambda e: e.weight, reverse=True)
    return out[:max_edges]


# -------------------------- Demo Workload (REAL) --------------------------

class DemoWorkload:
    """
    Real demo workload:
    - JSON: repeated loads + redundant parsing
    - array "image-ish": convolution + copies + normalization
    - async IO: concurrent fetch + sequential awaits anti-pattern
    - sqlite: N+1 queries + regex-ish filtering
    """
    @staticmethod
    def make_callable(optimized: bool, mem: MemoryRecorder) -> Callable[[], None]:
        rnd = random.Random(1337 if not optimized else 2024)

        def memo_checkpoint(label: str) -> None:
            mem.checkpoint(label)

        def demo_json_pipeline() -> int:
            # Build deterministic JSON payloads
            payloads = []
            for i in range(6):
                doc = {
                    "id": i,
                    "name": "user_" + str(i),
                    "tags": [rnd.choice(["alpha", "beta", "gamma", "delta"]) for _ in range(30)],
                    "events": [{"t": rnd.random(), "x": rnd.randint(0, 9999)} for _ in range(120)],
                }
                payloads.append(json.dumps(doc))

            import json as _json
            total = 0
            if not optimized:
                for s in payloads:
                    # redundant loads + nested re-serialization: intentionally wasteful
                    d = _json.loads(s)
                    tmp = _json.dumps(d)
                    d2 = _json.loads(tmp)
                    total += sum(ev["x"] for ev in d2["events"])
                # pathological: nested parsing of a field repeatedly
                nested = _json.dumps({"blob": payloads})
                parsed = _json.loads(nested)
                for item in parsed["blob"]:
                    d = _json.loads(item)
                    total += d["id"]
            else:
                # optimized: parse once; avoid dumps/loads loop
                for s in payloads:
                    d = _json.loads(s)
                    total += sum(ev["x"] for ev in d["events"])
                # avoid nested redundant parsing
                total += len(payloads)
            return total

        def demo_imageish_array() -> int:
            # a small "image": ints in [0..255]
            w, h = (220, 180) if not optimized else (220, 180)
            img = [rnd.randint(0, 255) for _ in range(w * h)]
            # allocate extra buffers (wasteful)
            if not optimized:
                buf = img[:]  # unnecessary copy
            else:
                buf = img  # reuse

            # 3x3 convolution (naive)
            kernel = [1, 2, 1, 2, 4, 2, 1, 2, 1]
            out = [0] * (w * h)
            for y in range(1, h - 1):
                row = y * w
                for x in range(1, w - 1):
                    acc = 0
                    idx = row + x
                    # unrolled neighborhood
                    acc += buf[idx - w - 1] * kernel[0]
                    acc += buf[idx - w] * kernel[1]
                    acc += buf[idx - w + 1] * kernel[2]
                    acc += buf[idx - 1] * kernel[3]
                    acc += buf[idx] * kernel[4]
                    acc += buf[idx + 1] * kernel[5]
                    acc += buf[idx + w - 1] * kernel[6]
                    acc += buf[idx + w] * kernel[7]
                    acc += buf[idx + w + 1] * kernel[8]
                    out[idx] = acc // 16

            # normalize + optional extra copies
            mx = max(out) or 1
            if not optimized:
                out2 = out[:]  # extra copy
            else:
                out2 = out
            norm = [(v * 255) // mx for v in out2]

            # allocate lots of small objects to hint alloc patterns
            if not optimized:
                junk = [{"p": v, "q": v ^ 123} for v in norm[:1800]]
                return sum(d["p"] for d in junk)
            return sum(norm[:3500])

        async def demo_async_io() -> int:
            async def fetch(endpoint: str) -> Dict[str, Any]:
                # simulate network + parsing + minor CPU
                await asyncio.sleep(0.03 + rnd.random() * 0.05)
                payload = {"endpoint": endpoint, "items": [rnd.randint(0, 9999) for _ in range(120)]}
                # intentionally JSON encode/decode to burn time
                s = json.dumps(payload)
                d = json.loads(s)
                return d

            endpoints = ["api/users", "api/products", "api/orders", "api/analytics"]
            # concurrent fetch
            res = await asyncio.gather(*(fetch(ep) for ep in endpoints))
            total = sum(sum(r["items"]) for r in res)

            if not optimized:
                # anti-pattern: sequential awaits
                for _ in range(4):
                    await asyncio.sleep(0.02)
                    total += 1
            else:
                await asyncio.gather(*(asyncio.sleep(0.02) for _ in range(4)))
                total += 4
            return total

        def demo_sqlite() -> int:
            con = sqlite3.connect(":memory:")
            cur = con.cursor()
            cur.execute("CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT)")
            cur.execute("CREATE TABLE orders (id INTEGER PRIMARY KEY, user_id INTEGER, amount REAL, message TEXT)")
            # insert
            users = [(i, f"user_{i}") for i in range(1, 101)]
            cur.executemany("INSERT INTO users(id,name) VALUES (?,?)", users)
            orders = []
            for i in range(1, 1001):
                uid = rnd.randint(1, 100)
                amt = rnd.random() * 200
                msg = rnd.choice(["ok", "warning", "error", "critical"]) + " " + ("x" * rnd.randint(5, 30))
                orders.append((i, uid, amt, msg))
            cur.executemany("INSERT INTO orders(id,user_id,amount,message) VALUES (?,?,?,?)", orders)
            con.commit()

            total = 0
            if not optimized:
                # N+1 pattern: query per user
                cur.execute("SELECT id FROM users LIMIT 60")
                uids = [r[0] for r in cur.fetchall()]
                for uid in uids:
                    cur.execute("SELECT amount FROM orders WHERE user_id = ?", (uid,))
                    rows = cur.fetchall()
                    total += int(sum(r[0] for r in rows))
            else:
                # batch (IN)
                cur.execute("SELECT id FROM users LIMIT 60")
                uids = [r[0] for r in cur.fetchall()]
                # build markers
                marks = ",".join(["?"] * len(uids))
                cur.execute(f"SELECT user_id, SUM(amount) FROM orders WHERE user_id IN ({marks}) GROUP BY user_id", uids)
                total += int(sum(r[1] for r in cur.fetchall()))

            # regex-ish slow filtering (simulated via Python regex on selected subset)
            cur.execute("SELECT message FROM orders LIMIT 800")
            msgs = [r[0] for r in cur.fetchall()]
            if not optimized:
                # backtracking suspect pattern (still bounded)
                pat = re.compile(r"(x+x+)+y")  # never matches; can backtrack on long x strings
                for m in msgs[:200]:
                    _ = pat.search(m + "y")  # likely match late
                    total += 1
            else:
                # safer pattern
                pat = re.compile(r"x{10,}y")
                for m in msgs[:200]:
                    _ = pat.search(m + "y")
                    total += 1

            con.close()
            return total

        def runner() -> None:
            # We weave in memory checkpoints between phases to make memory heatmap meaningful.
            memo_checkpoint("json:start")
            a = demo_json_pipeline()
            memo_checkpoint("json:end")

            memo_checkpoint("image:start")
            b = demo_imageish_array()
            memo_checkpoint("image:end")

            memo_checkpoint("async:start")
            c = asyncio.run(demo_async_io())
            memo_checkpoint("async:end")

            memo_checkpoint("sqlite:start")
            d = demo_sqlite()
            memo_checkpoint("sqlite:end")

            # tiny tail work so sampling sees a finishing phase
            s = 0
            for i in range(8000 if not optimized else 4000):
                s ^= (i * 2654435761) & 0xFFFFFFFF
            _ = (a + b + c + d + s)

        return runner


# -------------------------- Optimization Coach --------------------------

class OptimizationCoach:
    GLOSSARY = {
        "Flame Graph": "Blocks are stack frames. Width ~ time. Taller stacks are deeper call paths.",
        "Timeline": "Spans over time. Brush-select to zoom; double-click resets.",
        "Self Time": "Time spent inside a function excluding its callees.",
        "Cumulative Time": "Time spent in a function including all callees.",
        "N+1 Query": "Doing one query to fetch a list, then one query per item (many small queries).",
        "tracemalloc": "Stdlib allocator tracker. Shows where allocations happened (Python-level).",
        "Diff Mode": "Compare Run A vs Run B. Green = faster/less, Red = slower/more.",
    }

    def suggest(self, s: ProfileSession) -> List[Suggestion]:
        sug: List[Suggestion] = []
        # helper to add
        def add(sev: str, title: str, desc: str, evidence: str, action: str, link: str, cat: str) -> None:
            sug.append(Suggestion(severity=sev, title=title, description=desc, evidence=evidence, action=action, focus_link=link, category=cat))

        # detect N+1 in timeline spans (many similar SELECT ... WHERE user_id = N)
        db = [sp for sp in s.spans if sp.category == "db" or "SELECT" in sp.name.upper()]
        patterns: Dict[str, List[TimelineSpan]] = {}
        for sp in db:
            norm = re.sub(r"\b\d+\b", "N", sp.name)
            patterns.setdefault(norm, []).append(sp)
        for pat, spans in patterns.items():
            if len(spans) >= 10 and ("WHERE" in pat.upper()) and ("IN" not in pat.upper()):
                tot = sum(sp.dur for sp in spans)
                add(
                    "critical",
                    "N+1 Query Pattern Detected",
                    "Many similar queries executed in a loop. This is usually replaceable with one batched query (IN/JOIN).",
                    f"Pattern: {pat}\nCount: {len(spans)}\nApprox time: {_human_ms(tot)}",
                    "Batch with WHERE id IN (...) or JOIN; move loop work into SQL aggregation.",
                    Linker.focus_link("timeline", query=quote(pat)),
                    "database",
                )
                break

        # redundant JSON parsing
        json_hits = 0
        for r in s.top_funcs[:80]:
            fn = r.get("func", "")
            file = r.get("file", "")
            if ("json" in file.lower()) and (fn in ("loads", "dumps")):
                json_hits += int(r.get("calls", 0))
        if json_hits >= 200:
            top_json = [r for r in s.top_funcs if "json" in (r.get("file", "").lower())][:6]
            evid = "\n".join([f"{r.get('func')} { _human_ms(float(r.get('cum',0))) } • calls {r.get('calls')}" for r in top_json])
            add(
                "warning",
                "Excessive JSON encode/decode churn",
                "Lots of time spent in json.loads/json.dumps. Often a sign of redundant parsing or needless re-serialization.",
                evid or f"json calls ~ {json_hits}",
                "Parse once; pass dicts around; consider faster JSON libs for heavy pipelines (orjson) if compatible.",
                Linker.focus_link("flame", match="json"),
                "serialization",
            )

        # regex suspect (either Python regex internals or heavy re usage)
        regex_funcs = [r for r in s.top_funcs[:160] if "sre_" in r.get("func", "") or "re" in (r.get("file", "").lower())]
        if regex_funcs:
            worst = regex_funcs[0]
            add(
                "info",
                "Regex hot spot detected",
                "Regex can become expensive via backtracking, especially with nested quantifiers. Verify patterns on worst-case inputs.",
                f"{worst.get('func')} @ {_short_file(worst.get('file',''))}:{worst.get('line',0)} • cum {_human_ms(float(worst.get('cum',0)))}",
                "Prefer anchored patterns, avoid nested quantifiers, or pre-filter strings before regex.",
                Linker.focus_link("flame", match="re"),
                "regex",
            )

        # sequential awaits (timeline categories io with many small spans)
        io_spans = [sp for sp in s.spans if sp.category == "io"]
        if len(io_spans) >= 20:
            small = [sp for sp in io_spans if sp.dur < 0.03]
            if len(small) >= 8:
                tot = sum(sp.dur for sp in small)
                add(
                    "warning",
                    "IO micro-spans suggest sequential awaits",
                    "Many short IO waits in series can kill concurrency. Check for loops with 'await' inside.",
                    f"Short IO spans: {len(small)} • total {_human_ms(tot)}",
                    "Use asyncio.gather() to await concurrently, or raise concurrency limits with semaphores.",
                    Linker.focus_link("timeline", match="sleep"),
                    "concurrency",
                )

        # memory: too many allocations from same site or large peak
        if s.memory:
            peak = max(pt.peak for pt in s.memory)
            if peak > 120 * 1024 * 1024:
                add(
                    "warning",
                    "High peak memory usage",
                    "Peak memory is high for this run. Large temporary buffers or copies may be driving it.",
                    f"Peak: {_human_bytes(peak)} • checkpoints: {len(s.memory)}",
                    "Stream/chunk large data, reuse buffers, avoid copies; consider array views and in-place transforms.",
                    Linker.focus_link("memory", kind="peak"),
                    "memory",
                )
            # small alloc storm heuristic: high count at top sites
            top_counts = []
            for pt in s.memory:
                for site in pt.top:
                    top_counts.append(int(site.get("count", 0)))
            if top_counts and max(top_counts) > 25_000:
                add(
                    "info",
                    "Allocation storm (many small objects)",
                    "A hot allocation site is creating many objects. This often slows CPU and increases GC pressure.",
                    f"Max allocation count at a site: {max(top_counts)}",
                    "Prefer lists of primitives, reuse objects, preallocate, and avoid per-item dict creation in tight loops.",
                    Linker.focus_link("memory", kind="allocs"),
                    "memory",
                )

        # moved hotspot suggestion for Diff Mode is computed elsewhere; keep coach run-specific.

        # Add a tiny glossary boost (so tooltips feel “product”)
        if not sug:
            add(
                "info",
                "Nothing glaring detected",
                "This run looks fairly balanced. Use Diff Mode to compare changes after refactors.",
                "Tip: zoom into the flame graph, then bookmark hotspots and share perflens:// links with teammates.",
                "Try Diff Mode: run baseline then run an optimized variant.",
                Linker.focus_link("diff", kind="help"),
                "general",
            )

        # severity sort
        order = {"critical": 0, "warning": 1, "info": 2}
        sug.sort(key=lambda x: (order.get(x.severity, 9), x.category, x.title))
        return sug


# -------------------------- HTML Exporter (self-contained) --------------------------

class HtmlExporter:
    @staticmethod
    def export(session: ProfileSession, compare: Optional[ProfileSession] = None, theme: str = "dark") -> str:
        T = DARK if theme == "dark" else LIGHT
        title = f"PerfLens Report — {session.name}"
        created = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(session.created_at))

        flame_svg = HtmlExporter._flame_svg(session, compare, T)
        timeline_svg = HtmlExporter._timeline_svg(session, T)
        suggestions_html = HtmlExporter._suggestions_html(session)

        meta = {
            "name": session.name,
            "created_at": session.created_at,
            "duration_s": session.meta.get("duration_s", 0),
            "sample_count": session.meta.get("sample_count", 0),
            "error": session.meta.get("error", ""),
        }
        meta_json = _stable_json_dumps(meta)

        css = f"""
        :root {{
            --bg: {T['bg']};
            --panel: {T['panel']};
            --text: {T['text']};
            --muted: {T['muted']};
            --accent: {T['accent']};
            --accent2: {T['accent2']};
            --stroke: {T['stroke']};
            --chip: {T['chip']};
        }}
        html, body {{ background: var(--bg); color: var(--text); font-family: ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, Helvetica, Arial; }}
        .wrap {{ max-width: 1100px; margin: 28px auto; padding: 0 18px; }}
        .hdr {{ display:flex; justify-content:space-between; align-items:flex-end; gap:12px; }}
        .title {{ font-size: 26px; font-weight: 760; letter-spacing: -0.02em; }}
        .sub {{ color: var(--muted); font-size: 13px; }}
        .grid {{ display:grid; grid-template-columns: 1fr; gap: 14px; margin-top: 16px; }}
        .card {{ background: var(--panel); border: 1px solid var(--stroke); border-radius: 16px; overflow:hidden; box-shadow: 0 12px 30px rgba(0,0,0,0.18); }}
        .card h3 {{ margin: 0; padding: 12px 14px; border-bottom: 1px solid var(--stroke); font-size: 13px; color: var(--muted); letter-spacing: .02em; text-transform: uppercase; }}
        .card .content {{ padding: 10px 10px 14px 10px; }}
        .pill {{ display:inline-block; padding: 2px 10px; border-radius: 999px; background: var(--chip); border: 1px solid var(--stroke); color: var(--muted); font-size: 12px; margin-left: 8px; }}
        .tips {{ padding: 12px 14px; }}
        .sug {{ padding: 10px 14px; border-top: 1px solid var(--stroke); }}
        .sev-critical {{ color: #ff5c7c; font-weight: 700; }}
        .sev-warning {{ color: #ffcc66; font-weight: 700; }}
        .sev-info {{ color: #2ee59d; font-weight: 700; }}
        .mono {{ font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", "Courier New", monospace; }}
        .tipbox {{ position: fixed; pointer-events:none; z-index:999; display:none; background: rgba(20,24,34,0.92); color: #fff; border: 1px solid rgba(255,255,255,0.12); padding: 8px 10px; border-radius: 12px; max-width: 380px; font-size: 12px; }}
        a {{ color: var(--accent2); text-decoration: none; }}
        """

        js = """
        const tip = document.getElementById('tip');
        function showTip(html, x, y){
          tip.style.display = 'block';
          tip.innerHTML = html;
          const pad = 14;
          const w = tip.offsetWidth;
          const h = tip.offsetHeight;
          const nx = Math.min(window.innerWidth - w - pad, x + pad);
          const ny = Math.min(window.innerHeight - h - pad, y + pad);
          tip.style.left = nx + 'px';
          tip.style.top = ny + 'px';
        }
        function hideTip(){ tip.style.display = 'none'; }
        document.querySelectorAll('[data-tip]').forEach(el=>{
          el.addEventListener('mousemove', ev=> showTip(el.dataset.tip, ev.clientX, ev.clientY));
          el.addEventListener('mouseleave', hideTip);
        });
        """

        html = f"""<!doctype html>
<html>
<head>
<meta charset="utf-8"/>
<meta name="viewport" content="width=device-width, initial-scale=1"/>
<title>{title}</title>
<style>{css}</style>
</head>
<body>
<div class="wrap">
  <div class="hdr">
    <div>
      <div class="title">{title}</div>
      <div class="sub">Created {created} • Samples <span class="mono">{meta.get("sample_count",0)}</span> • Duration <span class="mono">{_human_ms(float(meta.get("duration_s",0)))}</span></div>
    </div>
    <div class="sub mono">PerfLens {APP_VERSION}</div>
  </div>

  <div class="grid">
    <div class="card">
      <h3>Flame Graph <span class="pill">hover blocks</span> <span class="pill">diff colors if provided</span></h3>
      <div class="content">{flame_svg}</div>
    </div>

    <div class="card">
      <h3>Timeline Trace <span class="pill">coalesced from samples</span></h3>
      <div class="content">{timeline_svg}</div>
    </div>

    <div class="card">
      <h3>Optimization Coach <span class="pill">heuristics</span></h3>
      <div class="tips">{suggestions_html}</div>
    </div>

    <div class="card">
      <h3>Run Metadata <span class="pill">deterministic JSON</span></h3>
      <div class="content"><pre class="mono" style="margin:0; white-space:pre-wrap;">{meta_json}</pre></div>
    </div>
  </div>
</div>
<div id="tip" class="tipbox"></div>
<script>{js}</script>
</body>
</html>
"""
        return html

    @staticmethod
    def _flame_svg(session: ProfileSession, compare: Optional[ProfileSession], T: Dict[str, str]) -> str:
        root = session.flame
        if not root:
            return "<div style='padding:12px; color: #999'>No flame</div>"

        # build a layout similar to widget
        width = 1040
        row_h = 20
        min_w = 2
        height = 300

        # map compare
        cmp_map: Dict[str, float] = {}
        if compare and compare.flame:
            for path, node in compare.flame.iter_nodes(()):
                cmp_map[" / ".join(path)] = node.value

        rects: List[Tuple[str, float, float, float, float, str]] = []  # key,x,y,w,h,label

        def place(node: FlameNode, x: float, y: float, w: float, path: Tuple[str, ...]) -> None:
            key = " / ".join(path + (node.name,))
            if w < min_w:
                return
            rects.append((key, x, y, w, row_h - 3, node.name))
            if not node.children:
                return
            base = max(1e-9, node.value)
            cx = x
            for _, ch in sorted(node.children.items(), key=lambda kv: kv[1].value, reverse=True):
                cw = w * (ch.value / base)
                place(ch, cx, y + row_h, cw, path + (node.name,))
                cx += cw

        place(root, 0, 0, width, tuple())
        max_y = max((y for _, _, y, _, _, _ in rects), default=0)
        height = int(max(240, max_y + row_h + 18))

        def color_for(key: str, node_value: float, node_self: float) -> str:
            if compare and key in cmp_map:
                b = cmp_map[key]
                if b <= 1e-9:
                    return T["bad"]
                ratio = node_value / b
                if ratio > 1.12:
                    return "#ff5c7c"
                if ratio < 0.88:
                    return "#2ee59d"
                return T["flame_warm"]
            # self ratio heat
            r = node_self / max(1e-9, node_value)
            # quick gradient
            cold = _qcolor(T["flame_cold"])
            warm = _qcolor(T["flame_warm"])
            hot = _qcolor(T["flame_hot"])
            if r < 0.5:
                c = _blend(cold, warm, r * 2)
            else:
                c = _blend(warm, hot, (r - 0.5) * 2)
            return c.name()

        # need node lookup for self_time
        val_map: Dict[str, Tuple[float, float]] = {}
        for path, node in root.iter_nodes(()):
            k = " / ".join(path)
            val_map[k] = (node.value, node.self_value)

        svg_parts = [f"<svg viewBox='0 0 {width} {height}' width='100%' height='{height}' style='background:{T['panel2']}; border-radius:12px; border:1px solid {T['stroke']}'>"]
        svg_parts.append(f"<style>.b{{cursor:default;}} .t{{font: 11px ui-sans-serif,system-ui; fill:{T['text']};}} .st{{stroke:{T['stroke']}; stroke-width:1;}}</style>")
        for key, x, y, w, h, label in rects:
            v, sv = val_map.get(key, (0.0, 0.0))
            col = color_for(key, v, sv)
            tip = f"{label} • total {_human_ms(v)} • self {_human_ms(sv)}"
            if compare and key in cmp_map:
                b = cmp_map[key]
                delta = v - b
                sign = "+" if delta >= 0 else ""
                tip += f" • Δ {sign}{_human_ms(delta)}"
            # Draw
            svg_parts.append(
                f"<g class='b' data-tip='{_html_escape(tip)}'>"
                f"<rect class='st' x='{x:.2f}' y='{y:.2f}' rx='4' ry='4' width='{max(0.0,w):.2f}' height='{h:.2f}' fill='{col}'/>"
            )
            if w > 70:
                lab = _html_escape(label[:30] + ("…" if len(label) > 30 else ""))
                svg_parts.append(f"<text class='t' x='{x+6:.2f}' y='{y+13:.2f}'>{lab}</text>")
            svg_parts.append("</g>")
        svg_parts.append("</svg>")
        return "".join(svg_parts)

    @staticmethod
    def _timeline_svg(session: ProfileSession, T: Dict[str, str]) -> str:
        spans = session.spans
        if not spans:
            return "<div style='padding:12px; color: #999'>No timeline</div>"

        width = 1040
        header = 28
        row_h = 22

        t0 = min(sp.start for sp in spans)
        t1 = max(sp.end for sp in spans)
        rng = max(1e-9, t1 - t0)

        # row assignment by category
        by_cat: Dict[str, List[TimelineSpan]] = {}
        for sp in spans:
            by_cat.setdefault(sp.category, []).append(sp)
        rows: Dict[str, int] = {}
        row_base = 0
        for cat in sorted(by_cat.keys()):
            ss = sorted(by_cat[cat], key=lambda x: (x.start, -x.dur))
            ends: List[float] = []
            for sp in ss[:1800]:  # cap
                placed = False
                for i in range(len(ends)):
                    if ends[i] <= sp.start:
                        rows[sp.span_id] = row_base + i
                        ends[i] = sp.end
                        placed = True
                        break
                if not placed:
                    rows[sp.span_id] = row_base + len(ends)
                    ends.append(sp.end)
            row_base += max(1, len(ends))
        height = int(max(240, header + (row_base + 2) * row_h))

        def tx(t: float) -> float:
            return (t - t0) / rng * width

        colors = {
            "cpu": T["accent"],
            "json": "#ff7a90",
            "db": "#fbbf24",
            "io": T["accent2"],
            "compute": "#60a5fa",
            "memory": "#a78bfa",
        }

        svg = [f"<svg viewBox='0 0 {width} {height}' width='100%' height='{height}' style='background:{T['panel2']}; border-radius:12px; border:1px solid {T['stroke']}'>"]
        svg.append(f"<style>.t{{font: 11px ui-sans-serif,system-ui; fill:{T['muted']};}} .lbl{{font: 10px ui-sans-serif,system-ui; fill:{T['text']};}}</style>")
        svg.append(f"<rect x='0' y='0' width='{width}' height='{header}' fill='{T['panel']}'/>")
        svg.append(f"<text class='t' x='12' y='18'>Timeline • brush/zoom in-app • spans coalesced from samples</text>")

        # grid
        ticks = 8
        for i in range(ticks + 1):
            x = width * (i / ticks)
            svg.append(f"<line x1='{x:.2f}' y1='{header}' x2='{x:.2f}' y2='{height}' stroke='{T['grid']}' stroke-width='1'/>")
            tt = t0 + rng * (i / ticks)
            svg.append(f"<text class='t' x='{x+3:.2f}' y='{header-6}'>{_html_escape(_human_ms(tt - t0))}</text>")

        # spans
        for sp in spans[:2500]:
            row = rows.get(sp.span_id, 0)
            x = tx(sp.start)
            w = max(3.0, tx(sp.end) - tx(sp.start))
            y = header + row * row_h + 4
            col = colors.get(sp.category, T["accent"])
            tip = f"{sp.name} • {_human_ms(sp.dur)} • {sp.category}"
            svg.append(f"<g data-tip='{_html_escape(tip)}'>")
            svg.append(f"<rect x='{x:.2f}' y='{y:.2f}' width='{w:.2f}' height='{row_h-8}' rx='4' ry='4' fill='{col}' opacity='0.95'/>")
            if w > 88:
                lab = sp.name
                if len(lab) > 24:
                    lab = lab[:23] + "…"
                svg.append(f"<text class='lbl' x='{x+6:.2f}' y='{y+12:.2f}'>{_html_escape(lab)}</text>")
            svg.append("</g>")

        svg.append("</svg>")
        return "".join(svg)

    @staticmethod
    def _suggestions_html(session: ProfileSession) -> str:
        if not session.suggestions:
            return "<div class='sub'>No suggestions</div>"
        parts = []
        for s in session.suggestions[:14]:
            cls = "sev-info"
            if s.severity == "critical":
                cls = "sev-critical"
            elif s.severity == "warning":
                cls = "sev-warning"
            parts.append(
                f"<div class='sug'>"
                f"<div><span class='{cls}'>{_html_escape(s.severity.upper())}</span> "
                f"<span class='pill'>{_html_escape(s.category)}</span></div>"
                f"<div style='margin-top:6px; font-weight:700'>{_html_escape(s.title)}</div>"
                f"<div style='margin-top:4px; color: var(--muted)'>{_html_escape(s.description)}</div>"
                f"<div style='margin-top:8px' class='mono'>{_html_escape(s.action)}</div>"
                f"</div>"
            )
        return "".join(parts)


def _html_escape(s: str) -> str:
    return (s or "").replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;")


# -------------------------- Background Worker --------------------------

class RunWorker(QObject):
    progress = Signal(int, str)
    finished = Signal(ProfileSession)
    failed = Signal(str, str)  # message, traceback
    cancelled = Signal()

    def __init__(self, fn: Callable[[], ProfileSession]) -> None:
        super().__init__()
        self.fn = fn

    def run(self) -> None:
        try:
            sess = self.fn()
            self.finished.emit(sess)
        except Cancelled:
            self.cancelled.emit()
        except Exception as e:
            tb = traceback.format_exc()
            self.failed.emit(f"{type(e).__name__}: {e}", tb)


# -------------------------- Command Palette --------------------------

@dataclass
class Command:
    title: str
    hint: str
    keys: str
    run: Callable[[], None]
    tags: str = ""


class CommandPalette(QDialog):
    def __init__(self, parent: QWidget, theme: Dict[str, str], commands: List[Command]) -> None:
        super().__init__(parent)
        self.theme = theme
        self.commands = commands
        self.setWindowTitle("Command Palette")
        self.setModal(True)
        self.setMinimumWidth(640)
        self.setMinimumHeight(420)

        root = QVBoxLayout(self)
        root.setContentsMargins(14, 14, 14, 14)

        self.q = QLineEdit(self)
        self.q.setPlaceholderText("Type a command…  (examples: theme, demo, diff, export, bookmark, open link)")
        root.addWidget(self.q)

        self.list = QListWidget(self)
        self.list.setSpacing(4)
        root.addWidget(self.list, 1)

        self.preview = QTextEdit(self)
        self.preview.setReadOnly(True)
        self.preview.setMinimumHeight(110)
        root.addWidget(self.preview)

        self.q.textChanged.connect(self._refresh)
        self.list.currentItemChanged.connect(self._preview)
        self.list.itemActivated.connect(self._activate)

        self._refresh()

    def setTheme(self, theme: Dict[str, str]) -> None:
        self.theme = theme
        self._refresh()

    def _score(self, cmd: Command, q: str) -> float:
        if not q:
            return 1.0
        hay = (cmd.title + " " + cmd.hint + " " + cmd.keys + " " + cmd.tags).lower()
        ql = q.lower()
        if ql in hay:
            return 3.0
        # fuzzy: subsequence
        i = 0
        for ch in ql:
            j = hay.find(ch, i)
            if j < 0:
                return 0.0
            i = j + 1
        return 1.6

    def _refresh(self) -> None:
        q = self.q.text().strip()
        scored = [(self._score(c, q), c) for c in self.commands]
        scored = [x for x in scored if x[0] > 0]
        scored.sort(key=lambda x: x[0], reverse=True)
        self.list.clear()
        for _, c in scored[:120]:
            item = QListWidgetItem(f"{c.title}")
            item.setData(Qt.UserRole, c)
            item.setToolTip(c.hint)
            self.list.addItem(item)
        if self.list.count():
            self.list.setCurrentRow(0)
        self._preview()

    def _preview(self) -> None:
        it = self.list.currentItem()
        if not it:
            self.preview.setHtml("")
            return
        c: Command = it.data(Qt.UserRole)
        html = (
            f"<div style='font-size:14px; font-weight:800'>{_html_escape(c.title)}</div>"
            f"<div style='margin-top:6px; color:{self.theme['muted']}'>{_html_escape(c.hint)}</div>"
            f"<div style='margin-top:10px; font-family: ui-monospace, Menlo, Consolas; color:{self.theme['text']};'>"
            f"{_html_escape(c.keys or '')}</div>"
        )
        self.preview.setHtml(html)

    def _activate(self, it: QListWidgetItem) -> None:
        c: Command = it.data(Qt.UserRole)
        self.accept()
        try:
            c.run()
        except Exception:
            QMessageBox.critical(self, "Command failed", traceback.format_exc())


# -------------------------- Main App UI --------------------------

class GlassCard(QFrame):
    def __init__(self, theme: Dict[str, str], title: str = "", subtitle: str = "") -> None:
        super().__init__()
        self.theme = theme
        self.setObjectName("GlassCard")
        lay = QVBoxLayout(self)
        lay.setContentsMargins(14, 12, 14, 12)
        lay.setSpacing(8)

        if title:
            t = QLabel(title)
            t.setObjectName("CardTitle")
            lay.addWidget(t)
        if subtitle:
            s = QLabel(subtitle)
            s.setObjectName("CardSubtitle")
            s.setWordWrap(True)
            lay.addWidget(s)


class MainWindow(QMainWindow):
    def __init__(self) -> None:
        super().__init__()
        self.setWindowTitle(f"{APP_NAME} • {APP_VERSION}")
        self.setMinimumSize(1200, 760)

        self.settings = QSettings("PerfLens", "PerfLensStudio")
        self.theme_name = self.settings.value("theme", "dark")
        self.theme = DARK if self.theme_name == "dark" else LIGHT

        self.profiler = PerformanceProfiler()
        self.sessions: List[ProfileSession] = []
        self.session_by_id: Dict[str, ProfileSession] = {}
        self.active: Optional[ProfileSession] = None
        self.compare: Optional[ProfileSession] = None

        self._thread: Optional[QThread] = None
        self._worker: Optional[RunWorker] = None

        # ---------- UI scaffold ----------
        self._build_actions()
        self._build_ui()
        self._apply_style()

        # first-run: auto-demo
        QTimer.singleShot(250, self.run_demo_baseline)

    # ----- UI -----

    def _build_actions(self) -> None:
        self.act_demo = QAction("Run Demo", self)
        self.act_demo.setShortcut(QKeySequence("Ctrl+R"))
        self.act_demo.triggered.connect(self.run_demo_baseline)

        self.act_demo_opt = QAction("Run Optimized Demo (for Diff)", self)
        self.act_demo_opt.triggered.connect(self.run_demo_optimized)

        self.act_profile_script = QAction("Profile Script…", self)
        self.act_profile_script.setShortcut(QKeySequence("Ctrl+O"))
        self.act_profile_script.triggered.connect(self.profile_script)

        self.act_profile_func = QAction("Profile Function…", self)
        self.act_profile_func.setShortcut(QKeySequence("Ctrl+P"))
        self.act_profile_func.triggered.connect(self.profile_function)

        self.act_deep_trace = QAction("Deep Trace (sys.setprofile) on last target", self)
        self.act_deep_trace.triggered.connect(self.deep_trace_last)

        self.act_export = QAction("Export HTML Report…", self)
        self.act_export.setShortcut(QKeySequence("Ctrl+E"))
        self.act_export.triggered.connect(self.export_html)

        self.act_save = QAction("Save Session…", self)
        self.act_save.setShortcut(QKeySequence("Ctrl+S"))
        self.act_save.triggered.connect(self.save_session)

        self.act_load = QAction("Load Session…", self)
        self.act_load.setShortcut(QKeySequence("Ctrl+L"))
        self.act_load.triggered.connect(self.load_session)

        self.act_theme = QAction("Toggle Theme", self)
        self.act_theme.setShortcut(QKeySequence("Ctrl+T"))
        self.act_theme.triggered.connect(self.toggle_theme)

        self.act_palette = QAction("Command Palette…", self)
        self.act_palette.setShortcut(QKeySequence("Ctrl+K"))
        self.act_palette.triggered.connect(self.open_palette)

        self.act_copy_link = QAction("Copy Focus Link", self)
        self.act_copy_link.setShortcut(QKeySequence("Ctrl+Shift+C"))
        self.act_copy_link.triggered.connect(self.copy_current_link)

        self.act_open_link = QAction("Open Link…", self)
        self.act_open_link.setShortcut(QKeySequence("Ctrl+Shift+O"))
        self.act_open_link.triggered.connect(self.open_link_dialog)

        self.act_add_bookmark = QAction("Bookmark Current Focus", self)
        self.act_add_bookmark.setShortcut(QKeySequence("Ctrl+D"))
        self.act_add_bookmark.triggered.connect(self.bookmark_current)

        self.act_cancel = QAction("Cancel Run", self)
        self.act_cancel.setShortcut(QKeySequence("Esc"))
        self.act_cancel.triggered.connect(self.cancel_run)

    def _build_ui(self) -> None:
        # menu
        m = self.menuBar()
        m.setNativeMenuBar(False)
        filem = m.addMenu("&File")
        filem.addAction(self.act_profile_script)
        filem.addAction(self.act_profile_func)
        filem.addSeparator()
        filem.addAction(self.act_save)
        filem.addAction(self.act_load)
        filem.addSeparator()
        filem.addAction(self.act_export)
        filem.addSeparator()
        filem.addAction("Quit", self.close)

        runm = m.addMenu("&Run")
        runm.addAction(self.act_demo)
        runm.addAction(self.act_demo_opt)
        runm.addSeparator()
        runm.addAction(self.act_deep_trace)
        runm.addSeparator()
        runm.addAction(self.act_cancel)

        viewm = m.addMenu("&View")
        viewm.addAction(self.act_theme)
        viewm.addAction(self.act_palette)
        viewm.addSeparator()
        viewm.addAction(self.act_copy_link)
        viewm.addAction(self.act_open_link)

        helpm = m.addMenu("&Help")
        helpm.addAction("Glossary (tooltips)", lambda: QMessageBox.information(self, "Glossary", "\n\n".join([f"{k}: {v}" for k, v in OptimizationCoach.GLOSSARY.items()])))
        helpm.addAction("About", lambda: QMessageBox.information(self, "About PerfLens", f"{APP_NAME} {APP_VERSION}\nA visual-first profiling studio.\n\nTip: Ctrl/Cmd+K opens the command palette."))

        # status
        self.status = QStatusBar(self)
        self.setStatusBar(self.status)
        self.status_label = QLabel("Ready")
        self.status.addWidget(self.status_label, 1)
        self.cancel_btn = QPushButton("Cancel")
        self.cancel_btn.clicked.connect(self.cancel_run)
        self.cancel_btn.setVisible(False)
        self.status.addPermanentWidget(self.cancel_btn)

        # layout: left sidebar + main tabs
        central = QWidget(self)
        self.setCentralWidget(central)
        root = QHBoxLayout(central)
        root.setContentsMargins(12, 12, 12, 12)
        root.setSpacing(12)

        split = QSplitter(Qt.Horizontal, central)
        root.addWidget(split, 1)

        # ----- left -----
        left = QWidget(split)
        left.setObjectName("Sidebar")
        left_l = QVBoxLayout(left)
        left_l.setContentsMargins(0, 0, 0, 0)
        left_l.setSpacing(10)

        brand = QLabel(f"{APP_NAME}")
        brand.setObjectName("Brand")
        left_l.addWidget(brand)

        self.search = QLineEdit()
        self.search.setPlaceholderText("Search everywhere… (flame, timeline, tables)")
        self.search.textChanged.connect(self.on_search)
        left_l.addWidget(self.search)

        # quick actions
        qa = QHBoxLayout()
        b1 = QPushButton("Run Demo")
        b1.clicked.connect(self.run_demo_baseline)
        b2 = QPushButton("Profile Script…")
        b2.clicked.connect(self.profile_script)
        qa.addWidget(b1, 1)
        qa.addWidget(b2, 1)
        left_l.addLayout(qa)

        qb = QHBoxLayout()
        b3 = QPushButton("Profile Function…")
        b3.clicked.connect(self.profile_function)
        b4 = QPushButton("Diff w/ Optimized")
        b4.clicked.connect(self.run_demo_optimized_and_diff)
        qb.addWidget(b3, 1)
        qb.addWidget(b4, 1)
        left_l.addLayout(qb)

        # sessions list
        box = QGroupBox("Runs")
        boxl = QVBoxLayout(box)
        boxl.setContentsMargins(10, 10, 10, 10)
        self.session_list = QListWidget()
        self.session_list.setObjectName("SessionList")
        self.session_list.itemSelectionChanged.connect(self.on_session_selected)
        boxl.addWidget(self.session_list, 1)
        left_l.addWidget(box, 1)

        # diff panel
        diff = QGroupBox("Diff Mode")
        diffl = QVBoxLayout(diff)
        diffl.setContentsMargins(10, 10, 10, 10)
        self.diff_toggle = QCheckBox("Enable Diff (A vs B)")
        self.diff_toggle.toggled.connect(self.apply_diff_mode)
        diffl.addWidget(self.diff_toggle)

        row = QHBoxLayout()
        self.diff_a = QComboBox()
        self.diff_b = QComboBox()
        self.diff_a.currentIndexChanged.connect(self.apply_diff_mode)
        self.diff_b.currentIndexChanged.connect(self.apply_diff_mode)
        row.addWidget(QLabel("A"))
        row.addWidget(self.diff_a, 1)
        row.addWidget(QLabel("B"))
        row.addWidget(self.diff_b, 1)
        diffl.addLayout(row)

        btns = QHBoxLayout()
        cpy = QPushButton("Copy Link")
        cpy.clicked.connect(self.copy_current_link)
        bm = QPushButton("Bookmark")
        bm.clicked.connect(self.bookmark_current)
        btns.addWidget(cpy, 1)
        btns.addWidget(bm, 1)
        diffl.addLayout(btns)

        left_l.addWidget(diff)

        # bookmarks
        bmx = QGroupBox("Bookmarks")
        bml = QVBoxLayout(bmx)
        bml.setContentsMargins(10, 10, 10, 10)
        self.bookmarks = QListWidget()
        self.bookmarks.setObjectName("BookmarkList")
        self.bookmarks.itemActivated.connect(self.open_bookmark)
        bml.addWidget(self.bookmarks, 1)
        left_l.addWidget(bmx, 1)

        split.addWidget(left)
        split.setStretchFactor(0, 0)

        # ----- main -----
        main = QWidget(split)
        main.setObjectName("MainPane")
        main_l = QVBoxLayout(main)
        main_l.setContentsMargins(0, 0, 0, 0)
        main_l.setSpacing(10)

        # top header
        hdr = QHBoxLayout()
        self.hdr_title = QLabel("Demo is running…")
        self.hdr_title.setObjectName("HeaderTitle")
        self.hdr_sub = QLabel("Sampling stacks + cProfile + tracemalloc • visual-first insights")
        self.hdr_sub.setObjectName("HeaderSubtitle")
        tbox = QVBoxLayout()
        tbox.addWidget(self.hdr_title)
        tbox.addWidget(self.hdr_sub)
        hdr.addLayout(tbox, 1)

        self.fancy_chip = QLabel("Ctrl/Cmd+K")
        self.fancy_chip.setObjectName("Chip")
        hdr.addWidget(self.fancy_chip)

        self.btn_palette = QToolButton()
        self.btn_palette.setText("⌘K")
        self.btn_palette.setToolTip("Command palette (Ctrl/Cmd+K)")
        self.btn_palette.clicked.connect(self.open_palette)
        hdr.addWidget(self.btn_palette)

        main_l.addLayout(hdr)

        # tabs
        self.tabs = QTabWidget()
        self.tabs.setObjectName("PrimaryTabs")
        main_l.addWidget(self.tabs, 1)

        # Studio tab: split flame + timeline
        studio = QWidget()
        studio_l = QVBoxLayout(studio)
        studio_l.setContentsMargins(0, 0, 0, 0)
        studio_l.setSpacing(10)

        studio_split = QSplitter(Qt.Vertical)
        studio_l.addWidget(studio_split, 1)

        self.flame = FlameGraphWidget(self.theme)
        self.flame.nodeClicked.connect(self.on_flame_clicked)
        self.flame.nodeHovered.connect(self.on_flame_hovered)
        studio_split.addWidget(self.flame)

        self.timeline = TimelineWidget(self.theme)
        self.timeline.spanClicked.connect(self.on_span_clicked)
        studio_split.addWidget(self.timeline)

        studio_split.setStretchFactor(0, 3)
        studio_split.setStretchFactor(1, 2)
        self.tabs.addTab(studio, "Studio")

        # Memory tab
        mem_tab = QWidget()
        mem_l = QVBoxLayout(mem_tab)
        mem_l.setContentsMargins(0, 0, 0, 0)
        mem_l.setSpacing(10)
        self.mem_heat = MemoryHeatmapWidget(self.theme)
        self.mem_heat.pointClicked.connect(self.on_mem_point_clicked)
        mem_l.addWidget(self.mem_heat, 1)

        self.mem_detail = QTextEdit()
        self.mem_detail.setReadOnly(True)
        self.mem_detail.setMinimumHeight(160)
        mem_l.addWidget(self.mem_detail)
        self.tabs.addTab(mem_tab, "Memory")

        # Call graph tab
        cg_tab = QWidget()
        cg_l = QVBoxLayout(cg_tab)
        cg_l.setContentsMargins(0, 0, 0, 0)
        cg_l.setSpacing(10)
        self.call_graph = CallGraphWidget(self.theme)
        self.call_graph.edgeClicked.connect(self.on_edge_clicked)
        cg_l.addWidget(self.call_graph, 1)

        self.cg_hint = QTextEdit()
        self.cg_hint.setReadOnly(True)
        self.cg_hint.setMinimumHeight(130)
        cg_l.addWidget(self.cg_hint)
        self.tabs.addTab(cg_tab, "Call Graph")

        # Coach tab
        coach_tab = QWidget()
        coach_l = QVBoxLayout(coach_tab)
        coach_l.setContentsMargins(0, 0, 0, 0)
        coach_l.setSpacing(10)

        top = QHBoxLayout()
        t = QLabel("Optimization Coach")
        t.setObjectName("CardTitle")
        top.addWidget(t)
        top.addStretch(1)
        self.btn_focus_sug = QPushButton("Focus Selected")
        self.btn_focus_sug.clicked.connect(self.focus_selected_suggestion)
        top.addWidget(self.btn_focus_sug)
        coach_l.addLayout(top)

        self.sug_model = SuggestionsModel()
        self.sug_table = QTableView()
        self.sug_table.setModel(self.sug_model)
        self.sug_table.setSelectionBehavior(QTableView.SelectRows)
        self.sug_table.setSelectionMode(QTableView.SingleSelection)
        self.sug_table.doubleClicked.connect(self.focus_selected_suggestion)
        self.sug_table.horizontalHeader().setStretchLastSection(True)
        self.sug_table.verticalHeader().setVisible(False)
        self.sug_table.setAlternatingRowColors(True)
        coach_l.addWidget(self.sug_table, 1)

        self.sug_detail = QTextEdit()
        self.sug_detail.setReadOnly(True)
        self.sug_detail.setMinimumHeight(160)
        coach_l.addWidget(self.sug_detail)
        self.sug_table.selectionModel().selectionChanged.connect(self.on_sug_sel)
        self.tabs.addTab(coach_tab, "Coach")

        # Stats tab (pstats)
        stats_tab = QWidget()
        stats_l = QVBoxLayout(stats_tab)
        stats_l.setContentsMargins(0, 0, 0, 0)
        stats_l.setSpacing(10)

        ts = QHBoxLayout()
        ts.addWidget(QLabel("Top Functions (cProfile/pstats)"))
        ts.addStretch(1)
        self.btn_copy_stats = QPushButton("Copy Table")
        self.btn_copy_stats.clicked.connect(self.copy_stats_table)
        ts.addWidget(self.btn_copy_stats)
        stats_l.addLayout(ts)

        self.top_model = TopFuncsModel()
        self.top_table = QTableView()
        self.top_table.setModel(self.top_model)
        self.top_table.setSelectionBehavior(QTableView.SelectRows)
        self.top_table.setSelectionMode(QTableView.SingleSelection)
        self.top_table.horizontalHeader().setStretchLastSection(True)
        self.top_table.verticalHeader().setVisible(False)
        self.top_table.setAlternatingRowColors(True)
        self.top_table.doubleClicked.connect(self.on_top_double_clicked)
        stats_l.addWidget(self.top_table, 1)

        self.stats_detail = QTextEdit()
        self.stats_detail.setReadOnly(True)
        self.stats_detail.setMinimumHeight(150)
        stats_l.addWidget(self.stats_detail)
        self.tabs.addTab(stats_tab, "Stats")

        split.addWidget(main)
        split.setStretchFactor(1, 1)
        split.setSizes([320, 900])

        # inspector dock-like panel on bottom of main
        self.inspector = QTextEdit()
        self.inspector.setReadOnly(True)
        self.inspector.setMinimumHeight(120)
        main_l.addWidget(self.inspector)

        # shortcuts
        self.addAction(self.act_palette)
        self.addAction(self.act_cancel)
        self.addAction(self.act_copy_link)
        self.addAction(self.act_add_bookmark)

    def _apply_style(self) -> None:
        # sleek QSS
        T = self.theme
        qss = f"""
        QMainWindow {{
            background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 {T['bg']}, stop:1 {T['panel2']});
            color: {T['text']};
            font-family: "Inter", "Segoe UI", "SF Pro Display", sans-serif;
        }}
        QWidget#Sidebar {{
            background: rgba(8, 16, 35, 0.78);
            border: 1px solid {T['stroke']};
            border-radius: 22px;
            padding: 16px;
        }}
        QWidget#MainPane {{
            background: rgba(10, 18, 36, 0.8);
            border: 1px solid {T['stroke']};
            border-radius: 26px;
            padding: 18px;
        }}
        QToolTip {{
            background: {T['panel']};
            border: 1px solid {T['stroke']};
            border-radius: 10px;
            padding: 6px 10px;
            color: {T['text']};
        }}
        QLabel#Brand {{
            font-size: 26px;
            font-weight: 900;
            letter-spacing: -0.05em;
            color: {T['text']};
            padding: 4px 8px;
        }}
        QLabel#HeaderTitle {{
            font-size: 19px;
            font-weight: 800;
            letter-spacing: -0.02em;
            color: {T['text']};
        }}
        QLabel#HeaderSubtitle {{
            font-size: 12px;
            color: {T['muted']};
        }}
        QLabel#Chip {{
            background: {T['chip']};
            border: 1px solid {T['stroke']};
            border-radius: 999px;
            padding: 6px 12px;
            color: {T['muted']};
            font-family: "SFMono-Regular", "Menlo", "Consolas";
        }}
        QLineEdit, QTextEdit {{
            background: {T['panel']};
            border: 1px solid {T['stroke']};
            border-radius: 14px;
            padding: 12px;
            selection-background-color: {T['accent']};
            color: {T['text']};
        }}
        QLineEdit:focus, QTextEdit:focus {{
            border: 1px solid {T['accent']};
            background: {T['panel2']};
        }}
        QPushButton, QToolButton {{
            background: qlineargradient(x1:0, y1:0, x2:1, y2:1, stop:0 {T['panel']}, stop:1 {T['panel2']});
            border: 1px solid rgba(255,255,255,0.08);
            border-radius: 14px;
            padding: 10px 14px;
            color: {T['text']};
            font-weight: 600;
            min-height: 36px;
        }}
        QPushButton:hover, QToolButton:hover {{
            border: 1px solid {T['accent']};
        }}
        QPushButton:pressed {{
            background: {T['panel2']};
        }}
        QToolButton {{
            border-radius: 16px;
        }}
        QGroupBox {{
            border: 1px solid {T['stroke']};
            border-radius: 16px;
            margin-top: 10px;
            background: rgba(9, 18, 36, 0.9);
            color: {T['muted']};
            padding-top: 24px;
        }}
        QGroupBox:title {{
            subcontrol-origin: margin;
            left: 16px;
            padding: 0 6px;
            color: {T['muted']};
            font-weight: 700;
        }}
        QListWidget, QTableView {{
            background: {T['panel']};
            border: 1px solid {T['stroke']};
            border-radius: 16px;
            padding: 6px;
            gridline-color: {T['grid']};
            color: {T['text']};
            alternate-background-color: {T['panel2']};
        }}
        QListWidget#SessionList {{
            padding: 10px;
        }}
        QListWidget#SessionList::item, QListWidget#BookmarkList::item {{
            padding: 10px 12px;
            border-radius: 12px;
            margin-bottom: 4px;
        }}
        QListWidget::item:hover {{
            background: rgba(255,255,255,0.06);
        }}
        QListWidget::item:selected {{
            background: {T['accent']};
            color: black;
        }}
        QTabWidget::pane {{
            border: 1px solid {T['stroke']};
            border-radius: 18px;
            padding: 12px;
            background: {T['panel2']};
        }}
        QTabWidget#PrimaryTabs::pane {{
            border-radius: 20px;
            padding: 14px;
        }}
        QTabBar::tab {{
            background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 {T['panel']}, stop:1 {T['panel2']});
            border: 1px solid {T['stroke']};
            border-bottom: none;
            padding: 9px 18px;
            border-top-left-radius: 16px;
            border-top-right-radius: 16px;
            margin-right: 6px;
            color: {T['muted']};
            font-weight: 600;
            letter-spacing: 0.3px;
        }}
        QTabBar::tab:selected {{
            background: {T['panel2']};
            color: {T['text']};
            border-color: {T['accent']};
        }}
        QTabBar::tab:hover {{
            color: {T['text']};
        }}
        QStatusBar {{
            background: {T['panel2']};
            border-top: 1px solid {T['stroke']};
            color: {T['muted']};
        }}
        QHeaderView::section {{
            background: {T['panel2']};
            color: {T['muted']};
            padding: 6px 8px;
            border: 1px solid {T['stroke']};
            border-radius: 8px;
        }}
        QCheckBox {{
            padding: 4px;
            color: {T['muted']};
        }}
        QCheckBox::indicator {{
            width: 18px;
            height: 18px;
            border-radius: 6px;
            border: 1px solid {T['stroke']};
            background: {T['panel']};
        }}
        QCheckBox::indicator:checked {{
            background: {T['accent']};
            border-color: {T['accent']};
        }}
        QComboBox, QSpinBox {{
            background: {T['panel']};
            border: 1px solid {T['stroke']};
            border-radius: 14px;
            padding: 8px 12px;
            color: {T['text']};
        }}
        QComboBox::drop-down {{
            border: none;
            width: 24px;
        }}
        QComboBox QAbstractItemView {{
            background: {T['panel']};
            border: 1px solid {T['stroke']};
            selection-background-color: {T['accent']};
            color: {T['text']};
        }}
        QSplitter::handle {{
            background: {T['stroke']};
            width: 2px;
            margin: 6px 0;
        }}
        QSplitter::handle:pressed {{
            background: {T['accent']};
        }}
        QTableView::item:selected {{
            background: rgba(111,157,255,0.18);
        }}
        QScrollBar:vertical {{
            width: 10px;
            background: transparent;
            margin: 14px 0 14px 0;
        }}
        QScrollBar::handle:vertical {{
            background: {T['stroke']};
            border-radius: 6px;
            min-height: 28px;
        }}
        QScrollBar::handle:vertical:hover {{
            background: {T['accent']};
        }}
        QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{
            height: 0px;
        }}
        QScrollBar:horizontal {{
            height: 10px;
            background: transparent;
            margin: 0 14px 0 14px;
        }}
        QScrollBar::handle:horizontal {{
            background: {T['stroke']};
            border-radius: 6px;
            min-width: 26px;
        }}
        QWidget#Sidebar QPushButton {{
            text-align: left;
        }}
        QListWidget#SessionList::item:selected:active {{
            background: {T['accent2']};
        }}
        """
        self.setStyleSheet(qss)

    # ----- State / Helpers -----

    def set_status(self, text: str) -> None:
        self.status_label.setText(text)

    def _set_running_ui(self, running: bool, label: str = "") -> None:
        self.cancel_btn.setVisible(running)
        if running:
            self.set_status(label or "Running…")
            self.hdr_title.setText("Profiling…")
            self.hdr_sub.setText(label or "Sampling stacks + cProfile + tracemalloc • live UI")
        else:
            self.set_status("Ready")
        # disable risky actions during run
        for a in [self.act_demo, self.act_demo_opt, self.act_profile_script, self.act_profile_func, self.act_save, self.act_export, self.act_deep_trace]:
            a.setEnabled(not running)

    def _add_session(self, sess: ProfileSession) -> None:
        self.sessions.insert(0, sess)
        self.session_by_id[sess.session_id] = sess
        # cap session history
        if len(self.sessions) > 20:
            old = self.sessions.pop()
            self.session_by_id.pop(old.session_id, None)

        item = QListWidgetItem(f"{sess.name}")
        item.setData(Qt.UserRole, sess.session_id)
        if "error" in sess.meta:
            item.setForeground(_qcolor(self.theme["bad"]))
            item.setToolTip(sess.meta.get("error", "Error"))
        else:
            item.setToolTip(f"{time.strftime('%H:%M:%S', time.localtime(sess.created_at))} • samples {sess.meta.get('sample_count',0)}")

        self.session_list.insertItem(0, item)
        self.session_list.setCurrentRow(0)
        self._refresh_diff_combo()
        self._refresh_bookmarks()

    def _refresh_diff_combo(self) -> None:
        # keep selection stable
        with QSignalBlocker(self.diff_a), QSignalBlocker(self.diff_b):
            cur_a = self.diff_a.currentData()
            cur_b = self.diff_b.currentData()
            self.diff_a.clear()
            self.diff_b.clear()
            for sess in self.sessions[:18]:
                label = sess.name
                self.diff_a.addItem(label, sess.session_id)
                self.diff_b.addItem(label, sess.session_id)
            # defaults: A = newest, B = second newest if possible
            if self.diff_a.count():
                self.diff_a.setCurrentIndex(0)
            if self.diff_b.count():
                self.diff_b.setCurrentIndex(min(1, self.diff_b.count() - 1))
            # try restore if still present
            if cur_a:
                i = self.diff_a.findData(cur_a)
                if i >= 0:
                    self.diff_a.setCurrentIndex(i)
            if cur_b:
                i = self.diff_b.findData(cur_b)
                if i >= 0:
                    self.diff_b.setCurrentIndex(i)

    def _refresh_bookmarks(self) -> None:
        self.bookmarks.clear()
        if not self.active:
            return
        for b in sorted(self.active.bookmarks, key=lambda x: x.created_at, reverse=True)[:60]:
            it = QListWidgetItem(b.name)
            it.setData(Qt.UserRole, b.link)
            it.setToolTip(b.note or b.link)
            self.bookmarks.addItem(it)

    def set_active(self, sess: Optional[ProfileSession]) -> None:
        self.active = sess
        if not sess:
            self.hdr_title.setText("No session selected")
            self.hdr_sub.setText("Run demo or profile your code.")
            self.flame.setData(None)
            self.timeline.setData([])
            self.mem_heat.setData([])
            self.call_graph.setData([])
            self.sug_model.set_rows([])
            self.top_model.set_rows([])
            self.inspector.setHtml("")
            self.mem_detail.setHtml("")
            self.cg_hint.setHtml("")
            self.sug_detail.setHtml("")
            self.stats_detail.setHtml("")
            self._refresh_bookmarks()
            return

        # header
        dur = _human_ms(float(sess.meta.get("duration_s", 0.0)))
        detail = f"Samples {sess.meta.get('sample_count',0)} • Duration {dur}"
        if sess.meta.get("has_deep_trace"):
            detail += " • Deep Trace ✓"
        if "error" in sess.meta:
            detail = f"<span style='color:{self.theme['bad']}'>Error</span> • {sess.meta.get('error','')}"
        self.hdr_title.setText(sess.name)
        self.hdr_sub.setText(detail)

        self.flame.setTheme(self.theme)
        self.timeline.setTheme(self.theme)
        self.mem_heat.setTheme(self.theme)
        self.call_graph.setTheme(self.theme)

        self.flame.setData(sess.flame)
        self.timeline.setData(sess.spans)
        self.mem_heat.setData(sess.memory)
        self.call_graph.setData(sess.call_edges)

        self.sug_model.set_rows(sess.suggestions)
        self.top_model.set_rows(sess.top_funcs)
        self._refresh_bookmarks()

        # inspector summary
        self.inspector.setHtml(self._session_summary_html(sess))

        # default details clean
        self.mem_detail.setHtml(self._memory_summary_html(sess))
        self.cg_hint.setHtml(self._cg_summary_html(sess))
        self.sug_detail.setHtml(self._coach_summary_html(sess))
        self.stats_detail.setHtml(self._stats_summary_html(sess))

        # apply diff mode if enabled
        self.apply_diff_mode(self.diff_toggle.isChecked())

    def _session_summary_html(self, s: ProfileSession) -> str:
        T = self.theme
        err = s.meta.get("error")
        html = f"<div style='font-weight:900; font-size:14px'>Run Summary</div>"
        html += f"<div style='color:{T['muted']}; margin-top:6px'>Created: {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(s.created_at))}</div>"
        html += f"<div style='margin-top:6px'>Duration: <b>{_human_ms(float(s.meta.get('duration_s',0)))}</b> • Samples: <b>{s.meta.get('sample_count',0)}</b> • Interval: <b>{float(s.meta.get('sample_interval_s',0))*1000:.2f}ms</b></div>"
        if err:
            html += f"<div style='color:{T['bad']}; margin-top:10px'><b>{_html_escape(err)}</b></div>"
            tb = s.meta.get("traceback", "")
            if tb:
                html += f"<pre style='background:{T['panel']}; border:1px solid {T['stroke']}; padding:10px; border-radius:12px; overflow:auto; margin-top:10px'>{_html_escape(tb)}</pre>"
        else:
            # top suggestion badges
            badges = []
            for sug in s.suggestions[:4]:
                col = T["good"]
                if sug.severity == "critical":
                    col = T["bad"]
                elif sug.severity == "warning":
                    col = T["warn"]
                badges.append(f"<span style='display:inline-block; padding:3px 8px; border-radius:999px; border:1px solid {T['stroke']}; background:{T['chip']}; margin-right:6px'><span style='color:{col}; font-weight:800'>{sug.severity.upper()}</span> <span style='color:{T['muted']}'>{_html_escape(sug.title)}</span></span>")
            if badges:
                html += "<div style='margin-top:10px'>" + "".join(badges) + "</div>"
        html += f"<div style='margin-top:10px; color:{T['muted']}'>Tip: Ctrl/Cmd+K for commands • Brush-select timeline to zoom • Middle-drag flame to pan</div>"
        return html

    def _memory_summary_html(self, s: ProfileSession) -> str:
        if not s.memory:
            return "<div style='color:gray'>No memory checkpoints.</div>"
        peak = max(pt.peak for pt in s.memory)
        cur = s.memory[-1].current
        return f"<b>Memory</b><br>Peak: <b>{_human_bytes(peak)}</b><br>End: <b>{_human_bytes(cur)}</b><br>Checkpoints: <b>{len(s.memory)}</b><br><br><span style='color:gray'>Click a heatmap column to inspect its top alloc sites.</span>"

    def _cg_summary_html(self, s: ProfileSession) -> str:
        if not s.call_edges:
            return "<div style='color:gray'>No call edges computed.</div>"
        top = s.call_edges[:8]
        lines = []
        for e in top:
            lines.append(f"{e.src} → {e.dst} • {_human_ms(e.weight)}")
        return "<b>Hot edges</b><br>" + "<br>".join([_html_escape(x) for x in lines]) + "<br><br><span style='color:gray'>Click edges to jump via flame search.</span>"

    def _coach_summary_html(self, s: ProfileSession) -> str:
        if not s.suggestions:
            return "<div style='color:gray'>No suggestions.</div>"
        top = s.suggestions[0]
        return f"<b>Top finding</b><br><b>{_html_escape(top.title)}</b><br><span style='color:gray'>{_html_escape(top.description)}</span><br><br><span style='color:gray'>Double-click a row to focus.</span>"

    def _stats_summary_html(self, s: ProfileSession) -> str:
        if not s.top_funcs:
            return "<div style='color:gray'>No cProfile stats.</div>"
        r = s.top_funcs[0]
        return f"<b>Top function (cProfile)</b><br>{_html_escape(r.get('func',''))}<br><span style='color:gray'>{_short_file(r.get('file',''))}:{r.get('line',0)}</span><br>Cum: <b>{_human_ms(float(r.get('cum',0)))}</b> • Self: <b>{_human_ms(float(r.get('self',0)))}</b> • Calls: <b>{r.get('calls',0)}</b>"

    # ----- Runs -----

    def _run_in_thread(self, build_session_fn: Callable[[], ProfileSession], label: str) -> None:
        if self._thread and self._thread.isRunning():
            QMessageBox.warning(self, "Busy", "A run is already in progress.")
            return
        self._set_running_ui(True, label)
        self.profiler.cancel_flag.clear()

        self._thread = QThread(self)
        self._worker = RunWorker(build_session_fn)
        thread = self._thread
        worker = self._worker
        worker.moveToThread(thread)

        thread.started.connect(worker.run)
        thread.finished.connect(thread.deleteLater)
        thread.finished.connect(lambda t=thread: self._clear_thread_ref(t))

        worker.finished.connect(thread.quit)
        worker.cancelled.connect(thread.quit)
        worker.failed.connect(lambda _msg, _tb, thr=thread: thr.quit())

        worker.finished.connect(worker.deleteLater)
        worker.cancelled.connect(worker.deleteLater)
        worker.failed.connect(lambda _msg, _tb, w=worker: w.deleteLater())
        worker.finished.connect(lambda w=worker: self._clear_worker_ref(w))
        worker.cancelled.connect(lambda w=worker: self._clear_worker_ref(w))
        worker.failed.connect(lambda _msg, _tb, w=worker: self._clear_worker_ref(w))

        worker.finished.connect(self._on_run_finished)
        worker.cancelled.connect(self._on_run_cancelled)
        worker.failed.connect(self._on_run_failed)

        thread.start()

    def _clear_worker_ref(self, worker: Optional[RunWorker]) -> None:
        if self._worker is worker:
            self._worker = None

    def _clear_thread_ref(self, thread: Optional[QThread]) -> None:
        if self._thread is thread:
            self._thread = None

    def cancel_run(self) -> None:
        if self._thread and self._thread.isRunning():
            self.profiler.cancel()
            self.set_status("Cancelling…")
            self.cancel_btn.setText("Cancelling…")
            self.cancel_btn.setEnabled(False)

    def _on_run_finished(self, sess: ProfileSession) -> None:
        self._set_running_ui(False)
        self.cancel_btn.setText("Cancel")
        self.cancel_btn.setEnabled(True)
        self._add_session(sess)
        self.set_active(sess)
        self.set_status("Done")

    def _on_run_cancelled(self) -> None:
        self._set_running_ui(False)
        self.cancel_btn.setText("Cancel")
        self.cancel_btn.setEnabled(True)
        self.set_status("Cancelled")

    def _on_run_failed(self, msg: str, tb: str) -> None:
        self._set_running_ui(False)
        self.cancel_btn.setText("Cancel")
        self.cancel_btn.setEnabled(True)
        self.set_status("Failed")
        QMessageBox.critical(self, "Run failed", msg + "\n\n" + tb)

    def run_demo_baseline(self) -> None:
        def build() -> ProfileSession:
            # hook memory checkpoints into demo callable
            mem = MemoryRecorder()
            runnable = DemoWorkload.make_callable(optimized=False, mem=mem)

            # wrap: we want demo to use our mem checkpoints; but MemoryRecorder in profiler is separate.
            # So we pass a "ghost" recorder that forwards by calling profiler's mem recorder via closure.
            # Easiest: rebuild the callable after profiler created MemoryRecorder; we do it below.
            # We'll instead implement memory checkpoints by executing runnable's code that calls mem.checkpoint(...)
            # where mem is the same MemoryRecorder used by profiler via closure in run_callable.
            # To do this, we create a new fn that uses profiler's recorder object.
            return self.profiler.run_callable(
                "Demo — Baseline (Real Workload)",
                fn=lambda: None,  # will be replaced below via monkey patch inside run_callable? not possible
            )

        # We need to pass the MemoryRecorder that run_callable uses into demo.
        # We'll do it by building a wrapper fn that *creates* the demo fn after MemoryRecorder exists.
        def build2() -> ProfileSession:
            # We'll reconstruct run_callable with a custom MemoryRecorder object exposed to DemoWorkload.
            # (PerformanceProfiler internally creates MemoryRecorder). To align, we temporarily override MemoryRecorder.checkpoint via callback.
            # Better: implement a "single source" by reusing MemoryRecorder external: small adaptation:
            pass

        # Instead of the above, use a custom run that parallels PerformanceProfiler but reuses its MemoryRecorder.
        self._run_demo(optimized=False)

    def run_demo_optimized(self) -> None:
        self._run_demo(optimized=True)

    def run_demo_optimized_and_diff(self) -> None:
        # run optimized, then enable diff vs last baseline if exists
        baseline = None
        for s in self.sessions:
            if "Demo — Baseline" in s.name:
                baseline = s
                break
        self._run_demo(optimized=True, after=lambda new_sess: self._auto_enable_diff(baseline, new_sess))

    def _auto_enable_diff(self, a: Optional[ProfileSession], b: Optional[ProfileSession]) -> None:
        if not a or not b:
            return
        # set comboboxes
        with QSignalBlocker(self.diff_toggle):
            self.diff_toggle.setChecked(True)
        ia = self.diff_a.findData(a.session_id)
        ib = self.diff_b.findData(b.session_id)
        if ia >= 0:
            self.diff_a.setCurrentIndex(ia)
        if ib >= 0:
            self.diff_b.setCurrentIndex(ib)
        self.apply_diff_mode(True)
        self.tabs.setCurrentIndex(0)

    def _run_demo(self, optimized: bool, after: Optional[Callable[[ProfileSession], None]] = None) -> None:
        label = "Running demo workload… (real JSON + compute + asyncio + sqlite)"
        self.cancel_btn.setText("Cancel")
        self.cancel_btn.setEnabled(True)

        def build() -> ProfileSession:
            # Create a MemoryRecorder that will be used by profiler, and pass it to demo callable.
            # We'll run a custom path that uses the same mem recorder (so demo checkpoints show up).
            self.profiler.cancel_flag.clear()
            session_id = hashlib.md5(f"{time.time()}:{random.random()}".encode()).hexdigest()[:12]
            name = "Demo — Optimized (for Diff)" if optimized else "Demo — Baseline (Real Workload)"
            sess = ProfileSession(session_id=session_id, name=name, created_at=time.time(), meta={"demo": True, "optimized": optimized})

            mem = MemoryRecorder()
            runnable = DemoWorkload.make_callable(optimized=optimized, mem=mem)

            # Use PerformanceProfiler but inject our mem by patching: easiest is to run its logic inline.
            sampler = SamplingCollector(interval_s=0.0013 if not optimized else 0.0013, max_samples=120_000)
            prof = cProfile.Profile()

            # cancellation trace
            counter = {"n": 0}
            def tracefunc(frame, event, arg):
                counter["n"] += 1
                if counter["n"] % 300 == 0 and self.profiler.cancel_flag.is_set():
                    raise Cancelled()
                return tracefunc

            target_tid = threading.get_ident()
            sampler.start(target_tid)
            import tracemalloc
            tracemalloc.start()
            mem._start_perf = time.perf_counter()
            mem.checkpoint("start")

            t0 = time.perf_counter()
            exc: Optional[BaseException] = None
            try:
                sys.settrace(tracefunc)
                prof.enable()
                runnable()
            except Cancelled as e:
                exc = e
            except BaseException as e:
                exc = e
            finally:
                try:
                    prof.disable()
                except Exception:
                    pass
                try:
                    sys.settrace(None)
                except Exception:
                    pass
                sampler.stop()
                try:
                    mem.checkpoint("end")
                except Exception:
                    pass
                try:
                    tracemalloc.stop()
                except Exception:
                    pass

            dur = max(1e-9, time.perf_counter() - t0)
            sess.samples = sampler.samples
            sess.memory = mem.points
            sess.flame = build_flame_from_samples(sess.samples)
            sess.spans = build_timeline_from_samples(sess.samples, max_spans=5200)
            sess.top_funcs = stats_top_funcs(prof, limit=200)
            sess.call_edges = call_edges_from_samples(sess.samples, max_edges=170)
            sess.suggestions = OptimizationCoach().suggest(sess)

            sess.meta["duration_s"] = dur
            sess.meta["sample_interval_s"] = sampler.interval
            sess.meta["sample_count"] = len(sess.samples)
            sess.meta["has_deep_trace"] = False
            sess.meta["target"] = {"type": "demo", "optimized": optimized}
            if exc:
                sess.meta["error"] = f"{type(exc).__name__}: {exc}"
                sess.meta["traceback"] = _trim_tb()
            return sess

        def after_hook(sess: ProfileSession) -> None:
            if after:
                after(sess)

        # Wrap to run after hook safely in UI thread after finished
        def build_with_after() -> ProfileSession:
            return build()

        # Run
        self._run_in_thread(build_with_after, label)

        # Attach after hook via a small timer once run is added (hook from _on_run_finished isn't parameterized).
        # We'll set a flag: if after present, store it and execute after setting active in _on_run_finished.
        self._pending_after = after_hook if after else None

    def _on_run_finished(self, sess: ProfileSession) -> None:
        super()._on_run_finished(sess) if hasattr(super(), "_on_run_finished") else None  # no-op safe
        # our original handler code
        self._set_running_ui(False)
        self.cancel_btn.setText("Cancel")
        self.cancel_btn.setEnabled(True)
        self._add_session(sess)
        self.set_active(sess)
        self.set_status("Done")
        # pending after hook
        hook = getattr(self, "_pending_after", None)
        self._pending_after = None
        if hook:
            try:
                hook(sess)
            except Exception:
                pass

    # ----- Profile Script / Function -----

    def profile_script(self) -> None:
        path, _ = QFileDialog.getOpenFileName(self, "Select Python Script", "", "Python (*.py)")
        if not path:
            return
        path = str(path)
        label = f"Profiling {Path(path).name}…"
        self.cancel_btn.setText("Cancel")
        self.cancel_btn.setEnabled(True)

        def build() -> ProfileSession:
            code = Path(path).read_text(encoding="utf-8", errors="replace")
            # isolated globals with a nice __file__
            g: Dict[str, Any] = {"__name__": "__main__", "__file__": path}
            # give users an optional helper for spans/checkpoints if they want
            # (no-op by default; still safe)
            def _noop_span(name: str, category: str = "cpu"):
                class Ctx:
                    def __enter__(self): return None
                    def __exit__(self, exc_type, exc, tb): return False
                return Ctx()
            g["perflens_span"] = _noop_span
            g["perflens_link"] = Linker.focus_link

            def runner() -> None:
                compiled = compile(code, path, "exec")
                exec(compiled, g, g)

            sess = self.profiler.run_callable(
                f"Script — {Path(path).name}",
                runner,
                sample_interval=0.0016,
                max_samples=160_000,
                include_deep_trace=False,
                meta={"target": {"type": "script", "path": path}},
            )
            return sess

        self._run_in_thread(build, label)

    def profile_function(self) -> None:
        # UX: ask for module or file + function name + args expr
        dlg = QDialog(self)
        dlg.setWindowTitle("Profile Function")
        dlg.setModal(True)
        lay = QVBoxLayout(dlg)
        lay.setContentsMargins(14, 14, 14, 14)

        form = QFormLayout()
        src = QLineEdit()
        src.setPlaceholderText("module.name OR /path/to/file.py")
        fn = QLineEdit()
        fn.setPlaceholderText("function_name (or dotted: obj.method)")
        args = QLineEdit()
        args.setPlaceholderText("args expression, e.g. () or (123, 'x') or {'n': 1000}")
        form.addRow("Source", src)
        form.addRow("Function", fn)
        form.addRow("Args", args)
        lay.addLayout(form)

        row = QHBoxLayout()
        ok = QPushButton("Profile")
        cancel = QPushButton("Cancel")
        row.addStretch(1)
        row.addWidget(cancel)
        row.addWidget(ok)
        lay.addLayout(row)

        cancel.clicked.connect(dlg.reject)
        ok.clicked.connect(dlg.accept)

        if dlg.exec() != QDialog.Accepted:
            return

        source = src.text().strip()
        func_name = fn.text().strip()
        arg_expr = args.text().strip() or "()"

        if not source or not func_name:
            QMessageBox.warning(self, "Missing info", "Please provide Source and Function.")
            return

        label = f"Profiling {func_name}…"
        self.cancel_btn.setText("Cancel")
        self.cancel_btn.setEnabled(True)

        def build() -> ProfileSession:
            # load module/file
            g: Dict[str, Any] = {}
            target_mod = None
            if source.endswith(".py") and Path(source).exists():
                code = Path(source).read_text(encoding="utf-8", errors="replace")
                g = {"__name__": "__perflens__", "__file__": source}
                exec(compile(code, source, "exec"), g, g)
                target_mod = types.SimpleNamespace(**g)
            else:
                import importlib
                target_mod = importlib.import_module(source)

            # resolve function
            obj: Any = target_mod
            for part in func_name.split("."):
                obj = getattr(obj, part)

            # eval args in a restricted-ish env
            safe_builtins = {"True": True, "False": False, "None": None, "range": range, "len": len, "min": min, "max": max, "sum": sum, "list": list, "dict": dict, "tuple": tuple}
            locs = {}
            globs = {"__builtins__": safe_builtins}
            try:
                parsed = eval(arg_expr, globs, locs)
            except Exception as e:
                raise RuntimeError(f"Args expression failed: {e}")

            call_args = ()
            call_kwargs = {}
            if isinstance(parsed, tuple):
                call_args = parsed
            elif isinstance(parsed, dict):
                call_kwargs = parsed
            else:
                call_args = (parsed,)

            def runner() -> None:
                obj(*call_args, **call_kwargs)

            meta = {"target": {"type": "function", "source": source, "func": func_name, "args": arg_expr}}
            sess = self.profiler.run_callable(f"Function — {func_name}", runner, sample_interval=0.0014, max_samples=140_000, include_deep_trace=False, meta=meta)
            return sess

        self._run_in_thread(build, label)

    def deep_trace_last(self) -> None:
        if not self.active:
            QMessageBox.information(self, "No session", "Run something first.")
            return
        tgt = self.active.meta.get("target") or {}
        if not tgt:
            QMessageBox.information(self, "No target info", "This session doesn't include a rerunnable target.")
            return

        label = "Deep tracing (sys.setprofile)…"
        self.cancel_btn.setText("Cancel")
        self.cancel_btn.setEnabled(True)

        def build() -> ProfileSession:
            t = tgt.get("type")
            if t == "demo":
                mem = MemoryRecorder()
                runnable = DemoWorkload.make_callable(optimized=bool(tgt.get("optimized")), mem=mem)
                sess = self.profiler.run_callable(
                    f"{self.active.name} • Deep Trace",
                    runnable,
                    sample_interval=float(self.active.meta.get("sample_interval_s", 0.0015)),
                    max_samples=int(self.active.meta.get("sample_count", 120_000) or 120_000),
                    include_deep_trace=True,
                    deep_trace_budget_s=1.8,
                    meta={"target": tgt, "deep_trace": True},
                )
                return sess
            if t == "script":
                path = tgt.get("path", "")
                if not path or not Path(path).exists():
                    raise RuntimeError("Script file no longer exists.")
                code = Path(path).read_text(encoding="utf-8", errors="replace")
                g: Dict[str, Any] = {"__name__": "__main__", "__file__": path}
                compiled = compile(code, path, "exec")
                def runner():
                    exec(compiled, g, g)
                return self.profiler.run_callable(f"Script — {Path(path).name} • Deep Trace", runner, include_deep_trace=True, meta={"target": tgt, "deep_trace": True})
            if t == "function":
                source = tgt.get("source", "")
                func_name = tgt.get("func", "")
                arg_expr = tgt.get("args", "()")
                # reuse profile_function loader
                g: Dict[str, Any] = {}
                target_mod = None
                if source.endswith(".py") and Path(source).exists():
                    code = Path(source).read_text(encoding="utf-8", errors="replace")
                    g = {"__name__": "__perflens__", "__file__": source}
                    exec(compile(code, source, "exec"), g, g)
                    target_mod = types.SimpleNamespace(**g)
                else:
                    import importlib
                    target_mod = importlib.import_module(source)
                obj: Any = target_mod
                for part in func_name.split("."):
                    obj = getattr(obj, part)
                safe_builtins = {"True": True, "False": False, "None": None, "range": range, "len": len, "min": min, "max": max, "sum": sum, "list": list, "dict": dict, "tuple": tuple}
                parsed = eval(arg_expr, {"__builtins__": safe_builtins}, {})
                call_args, call_kwargs = (), {}
                if isinstance(parsed, tuple):
                    call_args = parsed
                elif isinstance(parsed, dict):
                    call_kwargs = parsed
                else:
                    call_args = (parsed,)
                def runner():
                    obj(*call_args, **call_kwargs)
                return self.profiler.run_callable(f"Function — {func_name} • Deep Trace", runner, include_deep_trace=True, meta={"target": tgt, "deep_trace": True})
            raise RuntimeError("Unsupported target type for deep trace.")

        self._run_in_thread(build, label)

    # ----- Interactions -----

    def on_search(self, t: str) -> None:
        self.flame.setSearch(t)
        self.timeline.setSearch(t)
        self.top_model.set_filter(t)
        self.sug_model.set_filter(t)
        self.set_status(f"Search: {t}" if t else "Ready")

    def on_session_selected(self) -> None:
        items = self.session_list.selectedItems()
        if not items:
            return
        sid = items[0].data(Qt.UserRole)
        sess = self.session_by_id.get(sid)
        self.set_active(sess)

    def apply_diff_mode(self, enabled: bool) -> None:
        if not enabled:
            self.compare = None
            self.flame.setCompare(None)
            self.set_status("Diff mode off")
            return
        a_id = self.diff_a.currentData()
        b_id = self.diff_b.currentData()
        if not a_id or not b_id:
            return
        if a_id == b_id:
            self.set_status("Diff: choose different runs for A and B")
            self.flame.setCompare(None)
            return
        a = self.session_by_id.get(a_id)
        b = self.session_by_id.get(b_id)
        # convention: active = B (current), compare = A (baseline)
        # if active differs, switch active to B for clarity
        if b and (self.active is None or self.active.session_id != b.session_id):
            # don't break selection view, but we can set active if found in list.
            self.set_active(b)
        self.compare = a
        if self.active and self.compare:
            self.flame.setCompare(self.compare.flame)
            # augment coach with moved hotspots info (lightweight)
            self._diff_augment_suggestions(self.compare, self.active)
        self.set_status(f"Diff enabled: A={a.name if a else '—'} vs B={b.name if b else '—'}")

    def _diff_augment_suggestions(self, a: ProfileSession, b: ProfileSession) -> None:
        # add one synthetic suggestion: top regression & improvement in flame
        if not (a.flame and b.flame):
            return
        amap: Dict[str, float] = {}
        for path, node in a.flame.iter_nodes(()):
            amap[" / ".join(path)] = node.value
        deltas: List[Tuple[float, str, float, float]] = []
        for path, node in b.flame.iter_nodes(()):
            k = " / ".join(path)
            av = amap.get(k, 0.0)
            bv = node.value
            if av > 1e-6 or bv > 1e-6:
                deltas.append((bv - av, k, av, bv))
        deltas.sort(key=lambda x: x[0], reverse=True)
        if not deltas:
            return
        reg = deltas[0]
        imp = deltas[-1]
        extra: List[Suggestion] = []
        if reg[0] > 0.02:
            extra.append(Suggestion(
                severity="critical",
                title="Regression hotspot moved / grew",
                description="In Diff Mode, this frame grew in time compared to baseline A.",
                evidence=f"{reg[1]}\nA: {_human_ms(reg[2])}  B: {_human_ms(reg[3])}  Δ: +{_human_ms(reg[0])}",
                action="Click Focus to zoom to the hotspot, then inspect call context and allocations.",
                focus_link=Linker.focus_link("flame_path", path=quote(reg[1])),
                category="diff"
            ))
        if imp[0] < -0.02:
            extra.append(Suggestion(
                severity="info",
                title="Improvement detected",
                description="This frame got faster vs baseline A.",
                evidence=f"{imp[1]}\nA: {_human_ms(imp[2])}  B: {_human_ms(imp[3])}  Δ: {_human_ms(imp[0])}",
                action="If intentional, consider locking it in with a micro-benchmark and CI perf guardrails.",
                focus_link=Linker.focus_link("flame_path", path=quote(imp[1])),
                category="diff"
            ))
        if extra:
            # merge into active suggestions for UI (without mutating stored session permanently)
            # We'll show them at top in the model but keep session data consistent by cloning list in model.
            merged = extra + b.suggestions
            self.sug_model.set_rows(merged)

    def on_flame_clicked(self, path_key: str) -> None:
        self.flame.selected_path = path_key
        if self.active and self.active.flame:
            # find node quickly by scanning layout
            node = None
            for k, _, n, _ in self.flame._layout:
                if k == path_key:
                    node = n
                    break
            if node:
                self._set_inspector_for_node(path_key, node)
                # suggest timeline focus by search term
                self.timeline.setSearch(node.name)
        self.tabs.setCurrentIndex(0)

    def on_flame_hovered(self, path_key: str) -> None:
        # lightweight: show in status
        if path_key:
            self.set_status(f"Flame: {path_key}")

    def _set_inspector_for_node(self, path_key: str, node: FlameNode) -> None:
        T = self.theme
        html = f"<div style='font-weight:900'>Flame Focus</div>"
        html += f"<div style='margin-top:6px'><b>{_html_escape(node.name)}</b></div>"
        html += f"<div style='margin-top:6px'>Total: <b>{_human_ms(node.value)}</b> • Self: <b>{_human_ms(node.self_value)}</b></div>"
        if node.frame:
            html += f"<div style='margin-top:6px; color:{T['muted']}'>{_html_escape(node.frame.full)}</div>"
        link = Linker.focus_link("flame_path", path=quote(path_key))
        html += f"<div style='margin-top:10px; color:{T['muted']}'>Link: <span style='font-family:ui-monospace'>{_html_escape(link)}</span></div>"
        html += f"<div style='margin-top:6px; color:{T['muted']}'>Jargon: <b>Self Time</b> = excluding callees.</div>"
        self.inspector.setHtml(html)

    def on_span_clicked(self, span_id: str) -> None:
        if not self.active:
            return
        sp = next((x for x in self.active.spans if x.span_id == span_id), None)
        if not sp:
            return
        T = self.theme
        html = f"<div style='font-weight:900'>Timeline Focus</div>"
        html += f"<div style='margin-top:6px'><b>{_html_escape(sp.name)}</b> <span style='color:{T['muted']}'>({sp.category})</span></div>"
        html += f"<div style='margin-top:6px'>Duration: <b>{_human_ms(sp.dur)}</b> • Start: <b>{_human_ms(sp.start)}</b></div>"
        if sp.meta:
            html += "<div style='margin-top:8px; color:{}'>".format(T["muted"])
            for k, v in list(sp.meta.items())[:10]:
                html += f"{_html_escape(str(k))}: {_html_escape(str(v))}<br>"
            html += "</div>"
        link = Linker.focus_link("span", id=span_id)
        html += f"<div style='margin-top:10px; color:{T['muted']}'>Link: <span style='font-family:ui-monospace'>{_html_escape(link)}</span></div>"
        html += f"<div style='margin-top:6px; color:{T['muted']}'>Tip: brush-select to zoom in timeline.</div>"
        self.inspector.setHtml(html)

    def on_mem_point_clicked(self, idx: int) -> None:
        if not self.active or idx < 0 or idx >= len(self.active.memory):
            return
        pt = self.active.memory[idx]
        rows = pt.top[:14]
        T = self.theme
        html = f"<b>Memory checkpoint</b> — <span style='color:{T['muted']}'>{_html_escape(pt.label or '')}</span><br>"
        html += f"Current: <b>{_human_bytes(pt.current)}</b> • Peak: <b>{_human_bytes(pt.peak)}</b><br><br>"
        html += "<b>Top allocation sites</b><br>"
        for r in rows:
            html += f"<span style='font-family:ui-monospace'>{_html_escape(r.get('file',''))}:{r.get('line','')}</span> • {_human_bytes(int(r.get('size',0)))} • count {r.get('count',0)}<br>"
        self.mem_detail.setHtml(html)
        self.tabs.setCurrentIndex(1)

    def on_edge_clicked(self, src: str, dst: str) -> None:
        # Use global search to zoom view quickly
        self.search.setText(dst)
        self.tabs.setCurrentIndex(2)

    def on_sug_sel(self) -> None:
        # update detail box
        idx = self.sug_table.currentIndex()
        if not idx.isValid():
            return
        s: Suggestion = self.sug_table.model().data(idx.siblingAtColumn(0), Qt.UserRole)
        T = self.theme
        html = f"<div style='font-weight:900'>{_html_escape(s.title)}</div>"
        sev_col = T["good"]
        if s.severity == "critical":
            sev_col = T["bad"]
        elif s.severity == "warning":
            sev_col = T["warn"]
        html += f"<div style='margin-top:6px'><span style='color:{sev_col}; font-weight:800'>{s.severity.upper()}</span> <span style='color:{T['muted']}'>• {s.category}</span></div>"
        html += f"<div style='margin-top:10px; color:{T['text']}'>{_html_escape(s.description)}</div>"
        html += f"<div style='margin-top:10px; color:{T['muted']}'><b>Evidence</b><br><pre style='white-space:pre-wrap; background:{T['panel']}; border:1px solid {T['stroke']}; padding:10px; border-radius:12px'>{_html_escape(s.evidence)}</pre></div>"
        html += f"<div style='margin-top:10px'><b>Action</b><br><span style='font-family:ui-monospace'>{_html_escape(s.action)}</span></div>"
        if s.focus_link:
            html += f"<div style='margin-top:10px; color:{T['muted']}'>Jump: <span style='font-family:ui-monospace'>{_html_escape(s.focus_link)}</span></div>"
        self.sug_detail.setHtml(html)

    def focus_selected_suggestion(self) -> None:
        idx = self.sug_table.currentIndex()
        if not idx.isValid():
            return
        s: Suggestion = self.sug_table.model().data(idx.siblingAtColumn(0), Qt.UserRole)
        if not s.focus_link:
            return
        self.apply_link(s.focus_link)

    def on_top_double_clicked(self, idx: QModelIndex) -> None:
        if not idx.isValid():
            return
        r = self.top_table.model().data(idx.siblingAtColumn(0), Qt.UserRole)
        if not r:
            return
        func = r.get("func", "")
        file = r.get("file", "")
        self.stats_detail.setHtml(
            f"<b>{_html_escape(func)}</b><br><span style='color:gray'>{_html_escape(file)}:{r.get('line',0)}</span><br>"
            f"Cum: <b>{_human_ms(float(r.get('cum',0)))}</b> • Self: <b>{_human_ms(float(r.get('self',0)))}</b> • Calls: <b>{r.get('calls',0)}</b><br><br>"
            f"<span style='color:gray'>Tip: double-click suggests a flame search.</span>"
        )
        # jump via search
        self.search.setText(func)
        self.tabs.setCurrentIndex(3)

    # ----- Bookmarks & Links -----

    def current_link(self) -> str:
        # prioritize flame selection, else timeline selection
        if self.flame.selected_path:
            return Linker.focus_link("flame_path", path=quote(self.flame.selected_path))
        if self.timeline.selected:
            return Linker.focus_link("span", id=self.timeline.selected)
        return Linker.focus_link("session", id=(self.active.session_id if self.active else ""))

    def copy_current_link(self) -> None:
        link = self.current_link()
        QApplication.clipboard().setText(link)
        self.set_status("Copied link to clipboard")

    def bookmark_current(self) -> None:
        if not self.active:
            return
        link = self.current_link()
        kind = Linker.parse(link) or {}
        title = "Bookmark"
        if kind.get("kind") == "flame_path":
            title = "Flame: " + unquote(kind.get("path", ""))[-50:]
        elif kind.get("kind") == "span":
            title = "Timeline: " + kind.get("id", "")
        b = Bookmark(name=title, link=link, note="")
        self.active.bookmarks.append(b)
        self._refresh_bookmarks()
        self.set_status("Bookmarked")

    def open_bookmark(self, it: QListWidgetItem) -> None:
        link = it.data(Qt.UserRole)
        if link:
            self.apply_link(link)

    def open_link_dialog(self) -> None:
        dlg = QDialog(self)
        dlg.setWindowTitle("Open perflens:// Link")
        lay = QVBoxLayout(dlg)
        lay.setContentsMargins(14, 14, 14, 14)
        ed = QLineEdit()
        ed.setPlaceholderText("Paste a perflens://focus?... link")
        ed.setText(QApplication.clipboard().text().strip() if QApplication.clipboard().text().startswith("perflens://") else "")
        lay.addWidget(ed)
        row = QHBoxLayout()
        ok = QPushButton("Open")
        cancel = QPushButton("Cancel")
        row.addStretch(1)
        row.addWidget(cancel)
        row.addWidget(ok)
        lay.addLayout(row)
        cancel.clicked.connect(dlg.reject)
        ok.clicked.connect(dlg.accept)
        if dlg.exec() != QDialog.Accepted:
            return
        self.apply_link(ed.text().strip())

    def apply_link(self, link: str) -> None:
        parsed = Linker.parse(link)
        if not parsed:
            QMessageBox.warning(self, "Invalid link", "Not a perflens://focus link")
            return
        kind = parsed.get("kind", "")
        if kind == "session":
            sid = parsed.get("id", "")
            sess = self.session_by_id.get(sid)
            if sess:
                self.set_active(sess)
                self.tabs.setCurrentIndex(0)
                return
        if kind == "span":
            sid = parsed.get("id", "")
            self.tabs.setCurrentIndex(0)
            self.timeline.focusSpan(sid)
            self.on_span_clicked(sid)
            return
        if kind == "flame":
            match = parsed.get("match", "")
            if match:
                self.search.setText(unquote(match))
                self.tabs.setCurrentIndex(0)
            return
        if kind == "flame_path":
            path = unquote(parsed.get("path", ""))
            self.tabs.setCurrentIndex(0)
            self.flame.focusPath(path)
            # update inspector
            for k, _, n, _ in self.flame._layout:
                if k == path:
                    self._set_inspector_for_node(path, n)
                    break
            return
        if kind == "timeline":
            q = unquote(parsed.get("query", ""))
            if q:
                self.tabs.setCurrentIndex(0)
                self.search.setText(q)
                return
        if kind == "memory":
            # just open memory tab and show peak
            self.tabs.setCurrentIndex(1)
            self.set_status("Memory focus")
            return
        if kind == "diff":
            self.diff_toggle.setChecked(True)
            self.tabs.setCurrentIndex(0)
            return

    # ----- Save/Load/Export -----

    def save_session(self) -> None:
        if not self.active:
            return
        path, _ = QFileDialog.getSaveFileName(self, "Save Session", f"{self.active.name}.perflens.json", "PerfLens Session (*.json)")
        if not path:
            return
        Path(path).write_text(self.active.to_json(), encoding="utf-8")
        self.set_status("Saved session")

    def load_session(self) -> None:
        path, _ = QFileDialog.getOpenFileName(self, "Load Session", "", "PerfLens Session (*.json)")
        if not path:
            return
        s = Path(path).read_text(encoding="utf-8", errors="replace")
        sess = ProfileSession.from_json(s)
        sess.name = sess.name or Path(path).stem
        self._add_session(sess)
        self.set_active(sess)
        self.set_status("Loaded session")

    def export_html(self) -> None:
        if not self.active:
            return
        path, _ = QFileDialog.getSaveFileName(self, "Export HTML report", f"{self.active.name}.html", "HTML (*.html)")
        if not path:
            return
        html = HtmlExporter.export(self.active, self.compare if self.diff_toggle.isChecked() else None, theme=self.theme_name)
        Path(path).write_text(html, encoding="utf-8")
        self.set_status("Exported HTML report")
        # open in browser
        try:
            import webbrowser
            webbrowser.open("file://" + os.path.abspath(path))
        except Exception:
            pass

    # ----- Misc -----

    def copy_stats_table(self) -> None:
        rows = self.top_model._visible()
        lines = ["Function\tCum\tSelf\tCalls\tLocation"]
        for r in rows[:120]:
            lines.append(f"{r.get('func','')}\t{r.get('cum',0):.6f}\t{r.get('self',0):.6f}\t{r.get('calls',0)}\t{_short_file(r.get('file',''))}:{r.get('line',0)}")
        QApplication.clipboard().setText("\n".join(lines))
        self.set_status("Copied stats table")

    def toggle_theme(self) -> None:
        self.theme_name = "light" if self.theme_name == "dark" else "dark"
        self.settings.setValue("theme", self.theme_name)
        self.theme = DARK if self.theme_name == "dark" else LIGHT
        self._apply_style()
        # propagate
        self.flame.setTheme(self.theme)
        self.timeline.setTheme(self.theme)
        self.mem_heat.setTheme(self.theme)
        self.call_graph.setTheme(self.theme)
        # refresh details
        if self.active:
            self.set_active(self.active)
        self.set_status(f"Theme: {self.theme_name}")

    def open_palette(self) -> None:
        cmds = self._commands()
        dlg = CommandPalette(self, self.theme, cmds)
        dlg.exec()

    def _commands(self) -> List[Command]:
        cmds: List[Command] = [
            Command("Run Demo", "Run the built-in realistic workload (baseline).", "Ctrl+R", self.run_demo_baseline, tags="demo baseline"),
            Command("Run Optimized Demo", "Run optimized demo for Diff Mode.", "", self.run_demo_optimized, tags="demo diff optimized"),
            Command("Diff: Optimized vs Baseline", "Run optimized demo and enable Diff vs latest baseline.", "", self.run_demo_optimized_and_diff, tags="diff"),
            Command("Profile Script…", "Profile a .py script file.", "Ctrl+O", self.profile_script, tags="script open"),
            Command("Profile Function…", "Profile a function from a module or file.", "Ctrl+P", self.profile_function, tags="function"),
            Command("Deep Trace (sys.setprofile)", "Rerun last target to infer call edges using sys.setprofile (budgeted).", "", self.deep_trace_last, tags="deep trace setprofile"),
            Command("Export HTML Report…", "Export a self-contained report with SVG flame graph + timeline + findings.", "Ctrl+E", self.export_html, tags="export"),
            Command("Save Session…", "Save current session to deterministic JSON.", "Ctrl+S", self.save_session, tags="save"),
            Command("Load Session…", "Load a session from JSON.", "Ctrl+L", self.load_session, tags="load"),
            Command("Toggle Theme", "Switch between dark and light themes.", "Ctrl+T", self.toggle_theme, tags="theme"),
            Command("Copy Focus Link", "Copy perflens:// link that focuses the current selection.", "Ctrl+Shift+C", self.copy_current_link, tags="link share"),
            Command("Open Link…", "Paste a perflens:// link and jump to that focus.", "Ctrl+Shift+O", self.open_link_dialog, tags="link"),
            Command("Bookmark Current Focus", "Save the current focus into the session bookmarks.", "Ctrl+D", self.bookmark_current, tags="bookmark"),
            Command("Cancel Run", "Cancel the currently running profiling task.", "Esc", self.cancel_run, tags="cancel"),
            Command("Reset Flame View", "Reset flame zoom/pan.", "", self.flame.resetView, tags="flame zoom"),
            Command("Reset Timeline Zoom", "Reset timeline zoom to full range.", "", self.timeline.resetZoom, tags="timeline zoom"),
        ]
        return cmds


# -------------------------- App Bootstrap --------------------------

def main() -> None:
    # High DPI: Qt 6 is generally fine; keep crisp.
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    app.setOrganizationName("PerfLens")
    app.setOrganizationDomain("perflens.local")

    w = MainWindow()
    w.show()

    sys.exit(app.exec())


if __name__ == "__main__":
    main()
