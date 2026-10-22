#!/usr/bin/env python3
"""
Туристическая карта Сыктывкара: три артефакта из одного attractions.json.

    syktyvkar_map.svg        вектор A4 для печати и правки (Inkscape / Figma / Illustrator)
    syktyvkar_map.png        растр 2480×3508, 300 DPI, для вёрстки буклета
    attractions_legend.png   лист A4 с фото-миниатюрами 2×7, номера совпадают с картой
    index.html               автономная интерактивная карта для QR-кода
    syktyvkar_map.pdf        векторный PDF карты — на него ведёт «Скачать PDF»,
                             если рядом нет готового syktyvkar_booklet.pdf

Запуск:          python generate_map.py
Обновить OSM:    python generate_map.py --refresh-geo
Печать в CMYK:   python generate_map.py --cmyk ISOcoated_v2_eci.icc

Почему SVG собирается вручную, а не через svgwrite
--------------------------------------------------
* svgwrite заархивирован автором (последний релиз 1.4.3) — исправлений больше не будет;
* его валидатор не пропускает атрибуты, без которых не обойтись: inkscape:groupmode и
  inkscape:label (группы верхнего уровня открываются в Inkscape как слои) и data-* /
  role / tabindex для интерактивной версии внутри index.html;
* вся карта — это пять примитивов (g, path, circle, text, rect). Хелпер el() с
  экранированием через xml.sax.saxutils короче и прозрачнее обёртки над обёрткой,
  а одна функция render_svg(web=...) выдаёт и печатный, и веб-вариант.

Подложка (реки, парки, улицы) — выгрузка OpenStreetMap, закешированная в
geo/syktyvkar_osm.json, поэтому обычный запуск работает без сети.
"""
from __future__ import annotations

import argparse
import base64
import colorsys
import datetime as dt
import html
import io
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from xml.sax.saxutils import escape

from PIL import Image, ImageDraw, ImageEnhance, ImageFilter, ImageFont, ImageOps

# ─────────────────────────────── пути ───────────────────────────────

ROOT = Path(__file__).resolve().parent
DATA_FILE = ROOT / "attractions.json"
PHOTOS_DIR = ROOT / "photos"
GEO_CACHE = ROOT / "geo" / "syktyvkar_osm.json"
OUT_SVG = ROOT / "syktyvkar_map.svg"
OUT_PNG = ROOT / "syktyvkar_map.png"
OUT_LEGEND = ROOT / "attractions_legend.png"
OUT_HTML = ROOT / "index.html"
OUT_PDF = ROOT / "syktyvkar_map.pdf"
BOOKLET_PDF = ROOT / "syktyvkar_booklet.pdf"  # положите сюда свёрстанный буклет — кнопка поведёт на него

# Адрес, по которому будет лежать index.html (со слешем в конце). Нужен для абсолютных
# og:url / og:image — соцсети не понимают относительные ссылки. Пусто → относительные.
SITE_URL = ""

# ─────────────────────────────── страница ───────────────────────────────

PAGE_W, PAGE_H = 2480, 3508  # A4 портрет, 300 DPI
DPI = 300
SAFE = 177    # 15 мм — всё важное внутри этой рамки
BLEED = 118   # 10 мм — подложка уходит за обрез
BLEED_RECT = (-BLEED, -BLEED, PAGE_W + BLEED, PAGE_H + BLEED)
CLIP_RECT = (-BLEED - 30, -BLEED - 30, PAGE_W + BLEED + 30, PAGE_H + BLEED + 30)

# Окно, в которое вписываются центры маркеров. Справа оставлено место под подписи
# и столбец «Указатель», сверху — под заголовок, снизу — под легенду и линейку.
MAP_WINDOW = (SAFE + 120, SAFE + 520, PAGE_W - SAFE - 400, PAGE_H - SAFE - 600)

# ─────────────────────────────── палитра ───────────────────────────────

# Цвета категорий. Две светлые позиции из ТЗ (#F4A259, #FBC02D) затемнены: белый номер
# на них не читался (контраст 2.0 и 1.7). Если поставить светлый цвет, номер
# автоматически станет тёмным — см. on_color().
PALETTE = {
    "панно": "#6C63FF",
    "улица": "#8D6E63",
    "арт-объект": "#D46A1F",
    "памятник архитектуры": "#5C4033",
    "мемориал": "#C62828",
    "театр": "#7B1FA2",
    "скульптура": "#0288D1",
    "храм": "#B07F00",
    "кафе": "#2E7D32",
    "здание": "#546E7A",
}
FALLBACK_COLOR = "#455A64"

# Подложка — пастель с референса: песочная суша, кремовые улицы с тёмной окантовкой.
LAND = "#EDDDBB"
WATER = "#A8D5E2"
WATER_EDGE = "#7FB6C8"
WATER_TEXT = "#245A6C"
PARK = "#BFE3B0"
FOREST = "#D2E5BF"
STREET_MAJOR = "#E8E4D8"
STREET_MAJOR_CASING = "#C9B58C"
STREET_MINOR = "#FFFBF2"
RAIL = "#9A8C74"
RUNWAY = "#CDC3B0"
DISTRICT_LINE = "#9C8B6C"
DISTRICT_TEXT = "#575044"
LABEL_TEXT = "#2A2622"
MUTED_TEXT = "#62584B"
HALO = "#FFFFFF"
CARD = "#FFFDF7"
CARD_EDGE = "#D9C7A0"
YAH_RED = "#D32F2F"
LEGEND_BG = "#F7EFDD"

# ─────────────────────────────── типографика ───────────────────────────────

FONT_STACK = "'DejaVu Sans', Verdana, 'PT Sans', Arial, sans-serif"
FONT_FILES = {  # семейство → (обычный, жирный); первое найденное в системе используется для PNG
    "DejaVu Sans": (("DejaVuSans.ttf",), ("DejaVuSans-Bold.ttf",)),
    "Verdana": (("Verdana.ttf",), ("Verdana Bold.ttf", "verdanab.ttf")),
    "Arial": (("Arial.ttf",), ("Arial Bold.ttf", "arialbd.ttf")),
}
FONT_DIRS = [
    Path.home() / "Library/Fonts", Path("/Library/Fonts"), Path("/System/Library/Fonts/Supplemental"),
    Path("/usr/share/fonts"), Path("/usr/local/share/fonts"), Path.home() / ".local/share/fonts",
    Path.home() / ".fonts", Path("C:/Windows/Fonts"),
]

LABEL_SIZE = 32
LABEL_LINE_H = 38
LABEL_WRAP_W = 470          # длиннее — подпись переносится на две строки
HALO_W = 5                  # видимая толщина halo наружу; stroke-width = 2 × HALO_W
MARKER_R = 32               # диаметр 64
MARKER_STROKE = 6
MARKER_NUM_SIZE = 36
DISTRICT_SIZE = 32
DISTRICT_SPACING = 8
LABEL_GAP = 10              # от края маркера до подписи
LABEL_PAD = 6               # минимальный зазор между bbox
MAX_SHIFT_ITER = 3          # сдвигов по вертикали на каждую сторону
MAX_STREETS = 40
MAX_MAJOR_STREETS = 14

# Параметры, которые различаются в стилях (значения здесь — стиль «tz», строго по ТЗ)
MARKER_SHAPE = "circle"        # "circle" | "square"
MARKER_FILL = None             # None — цвет категории; иначе один цвет для всех маркеров
MARKER_EDGE = "#FFFFFF"
LABEL_ITALIC = False
LABEL_HALO = HALO
DISTRICT_CAPS = True
DISTRICT_BOLD = False
DISTRICT_HALO = None           # None — halo в цвет подложки под подписью
DISTRICT_BOUNDARIES = True
LEGEND_MODE = "categories"     # "categories" — цвета категорий; "list" — нумерованный список точек
STREET_MAJOR_W, STREET_MAJOR_CASING_W = 6, 10
STREET_MINOR_W, STREET_MINOR_CASING_W = 2, 0
STREET_MINOR_CASING = "#D3C29E"
RIVER_LABEL_BOLD = False

# ─────────────────────────────── координаты ───────────────────────────────

# Приблизительные координаты (lat, lon) по OpenStreetMap и справочникам, ±50–200 м.
# Точка из attractions.json с полями lat/lon имеет приоритет над этим словарём.
APPROX_COORDS: dict[int, tuple[float, float]] = {
    1: (61.66720, 50.84050),   # approximate — ул. Куратова, 17, торец дома (OSM way 1295252638)
    2: (61.66220, 50.81040),   # approximate — середина ряда домов 35–47 по Коммунистической (OSM nodes «Советский барельеф»)
    3: (61.66723, 50.84014),   # approximate — щель между корпусами Куратова, 17 (OSM node 6497415679)
    4: (61.67169, 50.82079),   # approximate — арт-объект у перекрёстка К. Маркса × Орджоникидзе (OSM node 6267672589)
    5: (61.67300, 50.83740),   # approximate — ул. Советская, 9 (OSM relation 9349531)
    6: (61.66670, 50.82436),   # approximate — мемориал «Вечная слава» (OSM node 700120904)
    7: (61.66958, 50.82506),   # approximate — ул. Первомайская, 56 (OSM way 648879687)
    8: (61.66964, 50.82724),   # approximate — памятник букве «Ӧ» (OSM node 1328432329)
    9: (61.66415, 50.85093),   # approximate — скульптура у аэровокзала (OSM node 9109472151)
    10: (61.66815, 50.83206),  # approximate — у ЦУМа, Интернациональная, 147 (OSM node 6141524513)
    11: (61.67785, 50.83144),  # approximate — ул. Свободы, 60 (OSM relation 13256003)
    12: (61.66690, 50.82746),  # approximate — ул. Первомайская, 72 (OSM node 9853634190)
    13: (61.66550, 50.83192),  # approximate — ул. Первомайская, 85 (OSM node 6089177018)
    14: (61.68550, 50.82502),  # approximate — ул. Петрозаводская, 4 (OSM way 1293415709)
}

# Центр города для заголовка и точек без координат: Стефановская площадь.
CITY_CENTER = (61.66854, 50.83521)  # approximate — OSM way 655501307

# «ВЫ ЗДЕСЬ»: Стефановская площадь — главная площадь, в двух кварталах от ЦУМа. Здесь
# логично ставить стенд с буклетом. Ровно у ЦУМа стоит маркер №10, поэтому точка
# не на нём, иначе её закроет маркер.
YOU_ARE_HERE = (61.66854, 50.83521)  # approximate

# Подписи районов (5–8 шт.): центры из OSM place=suburb. Реальных полигонов этих районов
# в OSM нет, поэтому границы схематичные — диаграмма Вороного по этим же центрам.
DISTRICTS: list[tuple[str, float, float]] = [
    ("Центр", 61.67000, 50.83300),           # approximate — своей точки в OSM нет, взят исторический центр
    ("Орбита", 61.69400, 50.81290),          # approximate — OSM node 8140551964
    ("Лесозавод", 61.65720, 50.87850),       # approximate — OSM node 8148029615
    ("Краснозатонский", 61.67420, 50.98020), # approximate — OSM node 11375039672, за краем листа
    ("Эжва", 61.79010, 50.74380),            # approximate — OSM node 3754421915, ~14 км к северу
    ("Кируль", 61.66590, 50.85800),          # approximate — OSM node 8355186749
    ("Строитель", 61.66830, 50.80180),       # approximate — OSM place=suburb
    ("Давпон", 61.64170, 50.80890),          # approximate — OSM node 6290257617
]

# ─────────────────────────────── OSM ───────────────────────────────

OVERPASS_URLS = [
    "https://overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
    "https://maps.mail.ru/osm/tools/overpass/api/interpreter",
]
GEO_BBOX = (61.615, 50.72, 61.725, 50.93)  # юг, запад, север, восток — с запасом вокруг листа

# ─────────────────────────────── фото ───────────────────────────────

ILLUSTRATIONS_DIR = ROOT / "illustrations"
SHOW_ILLUSTRATIONS = True  # мультяшные рисунки объектов на карте (как на референсе)
ILLU_SIZE = 230            # px, длинная сторона рисунка на карте (≈19 мм в печати)
ILLU_MAX_DIST = 660        # дальше от своего номера рисунок не уводим
SVG_NS = "http://www.w3.org/2000/svg"

THUMB = 600
LUT =(("Color", 1.05), ("Contrast", 1.08), ("Brightness", 1.02))  # единый для легенды и HTML
IMG_EXT = {".jpg", ".jpeg", ".png", ".webp", ".avif", ".heic"}

# ─────────────────────────────── стили ───────────────────────────────

# «tz»  — строго по ТЗ (имена файлов из ТЗ).
# «ref» — ближе к референсу sample-map: песочная суша, широкие кремовые улицы с окантовкой,
#         насыщенная зелень и вода, жёлтые квадратные номера, курсивные подписи, вместо
#         легенды категорий — нумерованный список. Файлы с суффиксом _ref.
# Стиль — это набор переопределений констант выше; остальное у стилей общее.
STYLES: dict[str, dict] = {
    "tz": {},
    "ref": {
        "LAND": "#DCC6A0",
        "WATER": "#6FB6EA",
        "WATER_EDGE": "#4F97CC",
        "WATER_TEXT": "#163F6E",
        "PARK": "#7FA97F",
        "FOREST": "#93B88C",
        "STREET_MAJOR": "#F6F0DF",
        "STREET_MAJOR_CASING": "#B49F7B",
        "STREET_MINOR": "#F1E8D2",
        "STREET_MINOR_CASING": "#C2AE8B",
        "STREET_MAJOR_W": 14, "STREET_MAJOR_CASING_W": 20,
        "STREET_MINOR_W": 6, "STREET_MINOR_CASING_W": 9,
        "RAIL": "#7D6B55",
        "RUNWAY": "#BFB39C",
        "LABEL_TEXT": "#231F1B",
        "LABEL_ITALIC": True,
        "LABEL_HALO": "#F7EEDC",
        "MARKER_SHAPE": "square",
        "MARKER_FILL": "#FFE81A",
        "MARKER_EDGE": "#1A1714",
        "MARKER_STROKE": 4,
        "DISTRICT_TEXT": "#2E2820",
        "DISTRICT_CAPS": False,
        "DISTRICT_BOLD": True,
        "DISTRICT_SIZE": 36,
        "DISTRICT_SPACING": 0,
        "DISTRICT_HALO": "#FFFFFF",
        "DISTRICT_BOUNDARIES": False,
        "LEGEND_MODE": "list",
        "RIVER_LABEL_BOLD": True,
        "CARD": "#FFF9EC",
        "CARD_EDGE": "#B49F7B",
        "OUT_SVG": ROOT / "syktyvkar_map_ref.svg",
        "OUT_PNG": ROOT / "syktyvkar_map_ref.png",
        "OUT_PDF": ROOT / "syktyvkar_map_ref.pdf",
        "OUT_LEGEND": ROOT / "attractions_legend_ref.png",
        "OUT_HTML": ROOT / "index_ref.html",
    },
}
_STYLE_BASE = {k: globals()[k] for s in STYLES.values() for k in s}


def use_style(name: str) -> None:
    """Сбрасывает константы к «tz» и накладывает переопределения стиля name."""
    globals().update(_STYLE_BASE)
    globals().update(STYLES[name])


WARNINGS: list[str] = []


def warn(msg: str) -> None:
    if msg in WARNINGS:  # одно и то же предупреждение — один раз, даже если стилей два
        return
    WARNINGS.append(msg)
    print(f"WARN  {msg}")


# ═══════════════════════════════ утилиты ═══════════════════════════════

def fmt(v: float) -> str:
    s = f"{v:.1f}"
    return s[:-2] if s.endswith(".0") else s


def hex_rgb(h: str) -> tuple[int, int, int]:
    h = h.lstrip("#")
    return int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)


def rgb_hex(rgb) -> str:
    return "#%02X%02X%02X" % tuple(max(0, min(255, round(c))) for c in rgb)


def rel_lum(h: str) -> float:
    def ch(c):
        c /= 255
        return c / 12.92 if c <= 0.03928 else ((c + 0.055) / 1.055) ** 2.4
    r, g, b = hex_rgb(h)
    return 0.2126 * ch(r) + 0.7152 * ch(g) + 0.0722 * ch(b)


def contrast(a: str, b: str) -> float:
    la, lb = sorted((rel_lum(a), rel_lum(b)), reverse=True)
    return (la + 0.05) / (lb + 0.05)


def mix(a: str, b: str, t: float) -> str:
    ra, rb = hex_rgb(a), hex_rgb(b)
    return rgb_hex(x + (y - x) * t for x, y in zip(ra, rb))


def brighter(h: str) -> str:
    """Цвет для подсветки при наведении: светлее и насыщеннее."""
    r, g, b = (c / 255 for c in hex_rgb(h))
    hh, ll, ss = colorsys.rgb_to_hls(r, g, b)
    r, g, b = colorsys.hls_to_rgb(hh, min(0.85, ll + 0.10), min(1.0, ss * 1.15))
    return rgb_hex((r * 255, g * 255, b * 255))


def on_color(h: str, large: bool = True) -> str:
    """Цвет номера на заливке: белый, если он читается. Порог WCAG: 3:1 для крупного
    жирного (номер на карте, 36 px), 4.5:1 для мелкого (бейдж в HTML, 15 px)."""
    return "#FFFFFF" if contrast("#FFFFFF", h) >= (3.0 if large else 4.5) else "#1F1B16"


def deepen(h: str, target: float = 4.5) -> str:
    """Тот же оттенок, затемнённый до контраста target с белым — для мелкого текста в HTML."""
    c = h
    for i in range(1, 21):
        if contrast("#FFFFFF", c) >= target:
            break
        c = mix(h, "#000000", i * 0.04)
    return c


def color_for(category: str) -> str:
    c = PALETTE.get(category)
    if c is None:
        warn(f"категории «{category}» нет в PALETTE — использован {FALLBACK_COLOR}")
        return FALLBACK_COLOR
    return c


def initials(name: str) -> str:
    words = [w for w in re.findall(r"[A-Za-zА-Яа-яЁё]+", name) if len(w) > 2]
    if not words:
        return (name.strip()[:1] or "?").upper()
    return (words[0][0] + (words[-1][0] if len(words) > 1 else "")).upper()


def short_name(street: str) -> str:
    """«улица Карла Маркса» → «карла маркса» — для сопоставления с адресами."""
    s = street.lower()
    for w in ("улица", "проспект", "переулок", "шоссе", "бульвар", "площадь", "проезд", "набережная", "ул.", "пр-т"):
        s = s.replace(w, " ")
    return " ".join(s.split())


def el(tag: str, attrs: dict | None = None, children=None) -> str:
    parts = []
    for k, v in (attrs or {}).items():
        if v is None or v is False:
            continue
        if isinstance(v, float):
            v = fmt(v)
        parts.append(f'{k}="{escape(str(v), {chr(34): "&quot;"})}"')
    a = (" " + " ".join(parts)) if parts else ""
    if isinstance(children, (list, tuple)):
        children = "\n".join(c for c in children if c)
    if not children:
        return f"<{tag}{a}/>"
    return f"<{tag}{a}>{children}</{tag}>"


# ═══════════════════════════════ шрифты ═══════════════════════════════

class Typo:
    """Измерение текста тем же шрифтом, которым будет отрисован PNG."""

    def __init__(self) -> None:
        index: dict[str, Path] = {}
        for d in FONT_DIRS:
            if d.is_dir():
                for p in d.rglob("*.tt[fc]"):
                    index.setdefault(p.name.lower(), p)
        self.family, self.paths = None, {False: None, True: None}
        for family, (regs, bolds) in FONT_FILES.items():
            reg = next((index[n.lower()] for n in regs if n.lower() in index), None)
            bold = next((index[n.lower()] for n in bolds if n.lower() in index), None)
            if reg and bold:
                self.family, self.paths = family, {False: reg, True: bold}
                break
        if self.family is None:
            warn("не найден ни DejaVu Sans, ни Verdana, ни Arial — ширина подписей оценена приблизительно")
        elif self.family != "DejaVu Sans":
            warn(f"DejaVu Sans не установлен — PNG/PDF отрисованы шрифтом {self.family} "
                 f"(в SVG остаётся стек «{FONT_STACK}»)")
        self._fonts: dict = {}

    def font(self, size: float, bold: bool = False):
        key = (round(size), bold)
        if key not in self._fonts:
            p = self.paths[bold]
            self._fonts[key] = ImageFont.truetype(str(p), key[0]) if p else ImageFont.load_default(size=key[0])
        return self._fonts[key]

    def width(self, text: str, size: float, bold: bool = False, spacing: float = 0.0) -> float:
        if self.family is None:
            w = 0.62 * size * len(text)
        else:
            w = self.font(size, bold).getlength(text)
        return w + spacing * max(len(text) - 1, 0)

    def wrap(self, text: str, size: float, max_w: float, bold: bool = False, max_lines: int = 3) -> list[str]:
        words = []
        for tok in glue(text).split(" "):
            # склейка шире строки — отпускаем неразрывные пробелы слева направо, пока не влезет
            while " " in tok and self.width(tok, size, bold) > max_w:
                head, tok = tok.split(" ", 1)
                words.append(head)
            words.append(tok)
        lines, cur = [], ""
        for word in words:
            cand = f"{cur} {word}".strip()
            if not cur or self.width(cand, size, bold) <= max_w:
                cur = cand
            else:
                lines.append(cur)
                cur = word
        if cur:
            lines.append(cur)
        if len(lines) > max_lines:
            lines = lines[:max_lines]
            lines[-1] = lines[-1].rstrip(" ,.—") + "…"
        return lines


def glue(text: str) -> str:
    """Неразрывные пробелы: название в «ёлочках» и короткие слова («на», «ул.», «им.», «В.»)
    не отрываются от следующего слова при переносе."""
    text = re.sub(r"«[^»]*»", lambda m: m.group(0).replace(" ", "\u00a0"), text)
    return re.sub(r"(?<!\S)(\S{1,3}) ", "\\1\u00a0", text)


def balanced_lines(text: str, typo: Typo, size: float, max_w: float) -> list[str]:
    """Одна строка, если влезает; иначе две строки примерно равной длины."""
    if typo.width(text, size) <= max_w:
        return [text]
    words = glue(text).split(" ")
    if len(words) < 2:
        return [text]
    best = min(range(1, len(words)),
               key=lambda i: max(typo.width(" ".join(words[:i]), size), typo.width(" ".join(words[i:]), size)))
    return [" ".join(words[:best]), " ".join(words[best:])]


# ═══════════════════════════════ геометрия ═══════════════════════════════

def m_per_deg(lat: float) -> tuple[float, float]:
    phi = math.radians(lat)
    lat_m = 111132.92 - 559.82 * math.cos(2 * phi) + 1.175 * math.cos(4 * phi)
    lon_m = 111412.84 * math.cos(phi) - 93.5 * math.cos(3 * phi)
    return lat_m, lon_m


@dataclass
class Projection:
    """Локальная равнопромежуточная проекция; на 5 км искажения меньше пикселя."""
    lat0: float
    lon0: float
    scale: float  # px на метр
    ox: float
    oy: float

    def __post_init__(self) -> None:
        self.mlat, self.mlon = m_per_deg(self.lat0)

    def xy(self, lat: float, lon: float) -> tuple[float, float]:
        return (self.ox + (lon - self.lon0) * self.mlon * self.scale,
                self.oy - (lat - self.lat0) * self.mlat * self.scale)

    def latlon(self, x: float, y: float) -> tuple[float, float]:
        return (self.lat0 - (y - self.oy) / (self.mlat * self.scale),
                self.lon0 + (x - self.ox) / (self.mlon * self.scale))

    def line(self, pts) -> list[tuple[float, float]]:
        return [self.xy(lat, lon) for lat, lon in pts]


def fit_projection(points: list[tuple[float, float]], window) -> Projection:
    lats, lons = [p[0] for p in points], [p[1] for p in points]
    lat0, lon0 = (min(lats) + max(lats)) / 2, (min(lons) + max(lons)) / 2
    mlat, mlon = m_per_deg(lat0)
    w_m = max((max(lons) - min(lons)) * mlon, 300)
    h_m = max((max(lats) - min(lats)) * mlat, 300)
    x0, y0, x1, y1 = window
    scale = min((x1 - x0) / w_m, (y1 - y0) / h_m)
    return Projection(lat0, lon0, scale, (x0 + x1) / 2, (y0 + y1) / 2)


def dp_simplify(pts, tol: float):
    """Дуглас — Пекер без рекурсии."""
    if len(pts) < 3:
        return list(pts)
    keep = [False] * len(pts)
    keep[0] = keep[-1] = True
    stack = [(0, len(pts) - 1)]
    while stack:
        i, j = stack.pop()
        (x1, y1), (x2, y2) = pts[i], pts[j]
        dx, dy = x2 - x1, y2 - y1
        l2 = dx * dx + dy * dy
        dmax, idx = 0.0, -1
        for k in range(i + 1, j):
            px, py = pts[k]
            t = 0.0 if l2 == 0 else max(0.0, min(1.0, ((px - x1) * dx + (py - y1) * dy) / l2))
            d = math.hypot(px - x1 - t * dx, py - y1 - t * dy)
            if d > dmax:
                dmax, idx = d, k
        if idx > 0 and dmax > tol:
            keep[idx] = True
            stack += [(i, idx), (idx, j)]
    return [p for p, k in zip(pts, keep) if k]


def _clip_half(pts, inside, cross):
    out = []
    if not pts:
        return out
    prev = pts[-1]
    for cur in pts:
        if inside(cur):
            if not inside(prev):
                out.append(cross(prev, cur))
            out.append(cur)
        elif inside(prev):
            out.append(cross(prev, cur))
        prev = cur
    return out


def clip_ring(ring, rect):
    """Сазерленд — Ходжмен по прямоугольнику."""
    x0, y0, x1, y1 = rect

    def at_x(x):
        return lambda p, q: (x, p[1] + (x - p[0]) * (q[1] - p[1]) / (q[0] - p[0]))

    def at_y(y):
        return lambda p, q: (p[0] + (y - p[1]) * (q[0] - p[0]) / (q[1] - p[1]), y)

    pts = _clip_half(list(ring), lambda p: p[0] >= x0, at_x(x0))
    pts = _clip_half(pts, lambda p: p[0] <= x1, at_x(x1))
    pts = _clip_half(pts, lambda p: p[1] >= y0, at_y(y0))
    pts = _clip_half(pts, lambda p: p[1] <= y1, at_y(y1))
    return pts


def clip_line(line, rect):
    """Обрезка ломаной по прямоугольнику (Лян — Барски), результат — список кусков."""
    x0, y0, x1, y1 = rect
    pieces, cur = [], []
    for (ax, ay), (bx, by) in zip(line, line[1:]):
        dx, dy = bx - ax, by - ay
        t0, t1, ok = 0.0, 1.0, True
        for p, q in ((-dx, ax - x0), (dx, x1 - ax), (-dy, ay - y0), (dy, y1 - ay)):
            if p == 0:
                if q < 0:
                    ok = False
                    break
            else:
                t = q / p
                if p < 0:
                    t0 = max(t0, t)
                else:
                    t1 = min(t1, t)
        if not ok or t0 > t1:
            if cur:
                pieces.append(cur)
                cur = []
            continue
        pa = (ax + t0 * dx, ay + t0 * dy)
        pb = (ax + t1 * dx, ay + t1 * dy)
        if cur and math.dist(cur[-1], pa) < 1e-6:
            cur.append(pb)
        else:
            if cur:
                pieces.append(cur)
            cur = [pa, pb]
        if t1 < 1.0:
            pieces.append(cur)
            cur = []
    if cur:
        pieces.append(cur)
    return [p for p in pieces if len(p) >= 2]


def line_len(pts) -> float:
    return sum(math.dist(a, b) for a, b in zip(pts, pts[1:]))


def ring_area(ring) -> float:
    return abs(sum(a[0] * b[1] - b[0] * a[1] for a, b in zip(ring, ring[1:] + ring[:1]))) / 2


def point_in_rings(x: float, y: float, rings) -> bool:
    inside = False
    for ring in rings:
        j = len(ring) - 1
        for i in range(len(ring)):
            (xi, yi), (xj, yj) = ring[i], ring[j]
            if (yi > y) != (yj > y) and x < (xj - xi) * (y - yi) / (yj - yi) + xi:
                inside = not inside
            j = i
    return inside


def voronoi_edges(sites, rect):
    """Рёбра диаграммы Вороного внутри rect: ячейка = прямоугольник, обрезанный
    полуплоскостями «ближе к своему центру». Для 8 районов O(n²) — мгновенно."""
    x0, y0, x1, y1 = rect
    edges = {}
    for i, (sx, sy) in enumerate(sites):
        cell = [(x0, y0), (x1, y0), (x1, y1), (x0, y1)]
        for j, (tx, ty) in enumerate(sites):
            if i == j:
                continue
            mx, my, nx, ny = (sx + tx) / 2, (sy + ty) / 2, tx - sx, ty - sy

            def cross(p, q, mx=mx, my=my, nx=nx, ny=ny):
                dp_ = (p[0] - mx) * nx + (p[1] - my) * ny
                dq = (q[0] - mx) * nx + (q[1] - my) * ny
                t = dp_ / (dp_ - dq)
                return p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])

            cell = _clip_half(cell, lambda p, mx=mx, my=my, nx=nx, ny=ny: (p[0] - mx) * nx + (p[1] - my) * ny <= 0, cross)
            if not cell:
                break
        for a, b in zip(cell, cell[1:] + cell[:1]):
            if math.dist(a, b) < 1:
                continue
            on_border = any(abs(a[k] - v) < 0.5 and abs(b[k] - v) < 0.5 for k, v in ((0, x0), (0, x1), (1, y0), (1, y1)))
            if not on_border:
                key = tuple(sorted([(round(a[0]), round(a[1])), (round(b[0]), round(b[1]))]))
                edges[key] = (a, b)
    return list(edges.values())


def merge_lines(lines):
    """Склеивает куски по общим концам (OSM дробит улицы и реки на десятки way)."""
    pool = [list(l) for l in lines if len(l) >= 2]
    out = []
    while pool:
        cur = pool.pop()
        grown = True
        while grown:
            grown = False
            for i, l in enumerate(pool):
                if l[0] == cur[-1]:
                    cur += l[1:]
                elif l[-1] == cur[-1]:
                    cur += l[-2::-1]
                elif l[-1] == cur[0]:
                    cur = l[:-1] + cur
                elif l[0] == cur[0]:
                    cur = l[:0:-1] + cur
                else:
                    continue
                pool.pop(i)
                grown = True
                break
        out.append(cur)
    return out


@dataclass
class Box:
    x0: float
    y0: float
    x1: float
    y1: float

    @property
    def cx(self) -> float:
        return (self.x0 + self.x1) / 2

    @property
    def cy(self) -> float:
        return (self.y0 + self.y1) / 2

    def hits(self, o: "Box", pad: float = 0.0) -> bool:
        return not (self.x1 + pad <= o.x0 or o.x1 + pad <= self.x0 or self.y1 + pad <= o.y0 or o.y1 + pad <= self.y0)

    def overlap(self, o: "Box") -> float:
        return max(0.0, min(self.x1, o.x1) - max(self.x0, o.x0)) * max(0.0, min(self.y1, o.y1) - max(self.y0, o.y0))

    def inside(self, o: "Box") -> bool:
        return self.x0 >= o.x0 and self.y0 >= o.y0 and self.x1 <= o.x1 and self.y1 <= o.y1

    def moved(self, dx: float = 0.0, dy: float = 0.0) -> "Box":
        return Box(self.x0 + dx, self.y0 + dy, self.x1 + dx, self.y1 + dy)


SAFE_BOX = Box(SAFE, SAFE, PAGE_W - SAFE, PAGE_H - SAFE)


# ═══════════════════════════════ данные ═══════════════════════════════

def load_attractions() -> tuple[dict, list[dict]]:
    raw = json.loads(DATA_FILE.read_text("utf-8"))
    meta = raw if isinstance(raw, dict) else {}
    items = raw["attractions"] if isinstance(raw, dict) else raw
    out, seen, todo = [], set(), 0
    for a in items:
        aid = int(a["id"])
        if aid in seen:
            raise SystemExit(f"attractions.json: id {aid} встречается дважды")
        seen.add(aid)
        lat, lon, src = a.get("lat"), a.get("lon"), "json"
        if lat is None or lon is None:
            if aid in APPROX_COORDS:
                (lat, lon), src = APPROX_COORDS[aid], "approx"
            else:
                # TODO: verify — координат нет: ставим в центр со сдвигом, чтобы точки не слиплись
                todo += 1
                lat, lon, src = CITY_CENTER[0] - 0.0012 * todo, CITY_CENTER[1] + 0.0015 * todo, "todo"
                warn(f"#{aid} «{a['name']}»: нет координат — поставлена у центра (TODO: verify)")
        out.append({**a, "id": aid, "lat": float(lat), "lon": float(lon), "coord_src": src,
                    "color": color_for(a.get("category", ""))})
    out.sort(key=lambda a: a["id"])
    return meta, out


# ═══════════════════════════════ OpenStreetMap ═══════════════════════════════

def overpass_query(bbox) -> str:
    s, w, n, e = bbox
    b = f"({s},{w},{n},{e})"
    return f"""[out:json][timeout:180];
(
  way["waterway"="river"]{b};
  way["natural"="water"]{b};
  relation["natural"="water"]{b};
  way["leisure"~"^(park|garden)$"]{b};
  relation["leisure"="park"]{b};
  way["landuse"="forest"]{b};
  way["natural"="wood"]{b};
  way["highway"~"^(trunk|primary|secondary|tertiary|residential|pedestrian|unclassified|living_street)$"]["name"]{b};
  way["railway"="rail"]{b};
  way["aeroway"="runway"]{b};
);
out geom qt;"""


def fetch_osm(bbox) -> list[dict]:
    body = urllib.parse.urlencode({"data": overpass_query(bbox)}).encode()
    for attempt in range(4):
        for url in OVERPASS_URLS:
            try:
                req = urllib.request.Request(url, data=body, headers={"User-Agent": "syktyvkar-tourist-map/1.0"})
                with urllib.request.urlopen(req, timeout=200) as r:
                    data = json.loads(r.read())
                print(f"OSM   выгружено через {url}: {len(data['elements'])} объектов")
                return data["elements"]
            except Exception as exc:  # сервера Overpass часто перегружены — пробуем следующий
                print(f"      {url}: {exc}")
        time.sleep(15 * (attempt + 1))
    raise SystemExit("Overpass недоступен — попробуйте позже или используйте закешированную geo/syktyvkar_osm.json")


def build_geo_cache(elements: list[dict], bbox) -> dict:
    lat0 = (bbox[0] + bbox[2]) / 2
    mlat, mlon = m_per_deg(lat0)

    def to_m(pts):
        return [(lon * mlon, lat * mlat) for lat, lon in pts]

    def simplify(pts, tol_m):
        if len(pts) < 3:
            return pts
        keep = dp_simplify(to_m(pts), tol_m)
        return [(round(y / mlat, 6), round(x / mlon, 6)) for x, y in keep]

    def geom(g):
        return [(p["lat"], p["lon"]) for p in g or [] if p]

    def area_m2(rings):
        return sum(ring_area(to_m(r)) for r in rings[:1])

    def rings_of(rel):
        outer = [geom(m.get("geometry")) for m in rel.get("members", []) if m.get("type") == "way" and m.get("role") in ("outer", "")]
        inner = [geom(m.get("geometry")) for m in rel.get("members", []) if m.get("type") == "way" and m.get("role") == "inner"]
        return [r for r in merge_lines(outer) + merge_lines(inner) if len(r) >= 4]

    water, parks, forests, rails, runways = [], [], [], [], []
    rivers: dict[str, list] = defaultdict(list)
    streets: dict[str, dict] = {}
    for e in elements:
        t = e.get("tags", {})
        if e["type"] == "relation":
            rings = rings_of(e)
            if not rings:
                continue
            if t.get("natural") == "water":
                water.append(rings)
            elif t.get("leisure") == "park":
                parks.append(rings)
            continue
        pts = geom(e.get("geometry"))
        if len(pts) < 2:
            continue
        closed = len(pts) >= 4 and pts[0] == pts[-1]
        if t.get("waterway") == "river":
            rivers[t.get("name", "")].append(pts)
        elif t.get("natural") == "water" and closed:
            water.append([pts])
        elif t.get("leisure") in ("park", "garden") and closed:
            parks.append([pts])
        elif (t.get("landuse") == "forest" or t.get("natural") == "wood") and closed:
            forests.append([pts])
        elif "highway" in t and t.get("name"):
            s = streets.setdefault(t["name"], {"hw": set(), "lines": []})
            s["hw"].add(t["highway"])
            s["lines"].append(pts)
        elif t.get("railway") == "rail":
            rails.append(pts)
        elif t.get("aeroway") == "runway":
            runways.append(pts)

    def poly_list(polys, min_area, tol):
        out = []
        for rings in polys:
            if area_m2(rings) >= min_area:
                out.append([simplify(r, tol) for r in rings])
        return out

    major_hw = {"trunk", "primary", "secondary"}
    cache = {
        "source": "© OpenStreetMap contributors, ODbL 1.0 — https://www.openstreetmap.org/copyright",
        "fetched": dt.date.today().isoformat(),
        "bbox": list(bbox),
        "water": poly_list(water, 1500, 3),
        "parks": poly_list(parks, 2500, 3),
        "forests": poly_list(forests, 40000, 6),
        "rivers": [{"name": n, "lines": [simplify(l, 3) for l in merge_lines(ls)]} for n, ls in rivers.items()],
        "streets": [
            {"name": n, "major": bool(s["hw"] & major_hw),
             "lines": [simplify(l, 2) for l in merge_lines(s["lines"])]}
            for n, s in sorted(streets.items())
            if sum(line_len(to_m(l)) for l in s["lines"]) >= 120
        ],
        "rails": [simplify(l, 4) for l in merge_lines(rails)],
        "runways": [simplify(l, 2) for l in runways],
    }
    return cache


def load_geo(args) -> dict:
    if args.osm_raw:
        elements = []
        for f in args.osm_raw:
            elements += json.loads(Path(f).read_text("utf-8"))["elements"]
        cache = build_geo_cache(elements, GEO_BBOX)
    elif args.refresh_geo or not GEO_CACHE.exists():
        if not GEO_CACHE.exists():
            print("OSM   кеша подложки нет — выгружаю из OpenStreetMap…")
        try:
            cache = build_geo_cache(fetch_osm(GEO_BBOX), GEO_BBOX)
        except SystemExit as exc:
            if GEO_CACHE.exists():
                warn(f"{exc}; оставлена старая подложка")
                return json.loads(GEO_CACHE.read_text("utf-8"))
            warn(f"{exc}; карта будет без подложки")
            return {"water": [], "parks": [], "forests": [], "rivers": [], "streets": [], "rails": [], "runways": []}
    else:
        return json.loads(GEO_CACHE.read_text("utf-8"))
    GEO_CACHE.parent.mkdir(parents=True, exist_ok=True)
    GEO_CACHE.write_text(json.dumps(cache, ensure_ascii=False, separators=(",", ":")), "utf-8")
    print(f"OSM   подложка сохранена: {GEO_CACHE} ({GEO_CACHE.stat().st_size // 1024} КБ)")
    return cache


# ═══════════════════════════════ сцена (раскладка) ═══════════════════════════════

@dataclass
class Label:
    aid: int
    lines: list[str]
    x: float           # центр маркера (уже после разведения маркеров)
    y: float
    w: float
    h: float
    side: str = "right"
    dy: float = 0.0
    box: Box | None = None
    collisions: int = 0
    placed: bool = False

    @property
    def shifted(self) -> bool:
        return self.placed and (self.side != "right" or abs(self.dy) > 0.5)


@dataclass
class Scene:
    meta: dict
    data: list[dict]
    proj: Projection
    water: list = field(default_factory=list)       # [[ring_px, …], …]
    parks: list = field(default_factory=list)
    forests: list = field(default_factory=list)
    rivers: list = field(default_factory=list)      # [(name, [line_px, …])]
    river_labels: list = field(default_factory=list)
    streets_major: list = field(default_factory=list)  # [(name, [line_px, …])]
    streets_minor: list = field(default_factory=list)
    rails: list = field(default_factory=list)
    runways: list = field(default_factory=list)
    district_edges: list = field(default_factory=list)
    district_labels: list = field(default_factory=list)
    labels: list[Label] = field(default_factory=list)
    index: list[dict] = field(default_factory=list)
    illustrations: list[dict] = field(default_factory=list)
    ui: dict = field(default_factory=dict)          # имя → Box
    yah: dict = field(default_factory=dict)
    has_geo: bool = True


def label_box(lab: Label, side: str, dy: float) -> Box:
    r = MARKER_R + MARKER_STROKE / 2
    cy = lab.y + dy
    if side == "right":
        x0 = lab.x + r + LABEL_GAP
        return Box(x0, cy - lab.h / 2, x0 + lab.w, cy + lab.h / 2)
    x1 = lab.x - r - LABEL_GAP
    return Box(x1 - lab.w, cy - lab.h / 2, x1, cy + lab.h / 2)


def place_labels(labels: list[Label], obstacles: list[Box], bounds: Box) -> list[Label]:
    """Жадная раскладка. Сначала подпись справа; при пересечении bbox — до трёх
    сдвигов по вертикали (каждый уводит подпись от самого глубокого пересечения);
    не вышло — то же слева; не вышло и там — подпись уходит в «Указатель»."""
    placed: list[Box] = []
    max_dy = 2.6 * LABEL_LINE_H

    def crowd(lab):
        return -sum(1 for o in labels if o is not lab and math.dist((o.x, o.y), (lab.x, lab.y)) < 420)

    for lab in sorted(labels, key=lambda l: (crowd(l), l.aid)):
        for side in ("right", "left"):
            dy = 0.0
            for it in range(MAX_SHIFT_ITER + 1):
                box = label_box(lab, side, dy)
                hits = [o for o in obstacles + placed if box.hits(o, LABEL_PAD)]
                if not hits and box.inside(bounds):
                    lab.side, lab.dy, lab.box, lab.placed = side, dy, box, True
                    break
                lab.collisions += 1
                if it == MAX_SHIFT_ITER:
                    break
                if hits:
                    o = max(hits, key=box.overlap)
                    if box.cy <= o.cy:
                        dy -= box.y1 - o.y0 + LABEL_PAD
                    else:
                        dy += o.y1 - box.y0 + LABEL_PAD
                elif box.y0 < bounds.y0:
                    dy += bounds.y0 - box.y0
                elif box.y1 > bounds.y1:
                    dy -= box.y1 - bounds.y1
                else:
                    break  # вылезла за поле по горизонтали — эта сторона не годится
                if abs(dy) > max_dy:
                    break
            if lab.placed:
                placed.append(lab.box)
                break
    return labels


def spread_markers(pts: dict[int, tuple[float, float]]) -> dict[int, tuple[float, float]]:
    """Разводит маркеры, которые наползают друг на друга (№1 и №3 — один дом, 20 м).
    Истинная точка остаётся на карте маленькой точкой с выноской к кружку."""
    pos = {k: list(v) for k, v in pts.items()}
    touch_d = 2 * MARKER_R + MARKER_STROKE + 4   # ближе — кружки слипаются
    min_d = 2 * MARKER_R + MARKER_STROKE + 34    # разводим до зазора, в котором видна истинная точка
    clash = {(a, b) for a in pos for b in pos if a < b and math.dist(pts[a], pts[b]) < touch_d}
    for _ in range(200):
        moved = False
        ids = list(pos)
        for i, a in enumerate(ids):
            for b in ids[i + 1:]:
                (ax, ay), (bx, by) = pos[a], pos[b]
                d = math.hypot(bx - ax, by - ay)
                if d < (min_d if (a, b) in clash else touch_d):
                    if d < 1e-6:
                        ux, uy = 1.0, 0.0
                    else:
                        ux, uy = (bx - ax) / d, (by - ay) / d
                    push = (min_d - d) / 2 + 0.5
                    pos[a][0] -= ux * push
                    pos[a][1] -= uy * push
                    pos[b][0] += ux * push
                    pos[b][1] += uy * push
                    moved = True
        if not moved:
            break
    return {k: (v[0], v[1]) for k, v in pos.items()}


def build_scene(meta: dict, data: list[dict], geo: dict, typo: Typo) -> Scene:
    proj = fit_projection([(a["lat"], a["lon"]) for a in data], MAP_WINDOW)
    sc = Scene(meta, data, proj, has_geo=bool(geo.get("streets")))

    # ── подложка
    def polys(key, tol=1.0, min_area=40.0):
        out = []
        for rings in geo.get(key, []):
            px = []
            for r in rings:
                c = clip_ring(proj.line(r), CLIP_RECT)
                if len(c) >= 3:
                    c = dp_simplify(c + [c[0]], tol)[:-1]
                    if len(c) >= 3 and ring_area(c) >= min_area:
                        px.append(c)
            if px:
                out.append(px)
        return out

    def lines(raw, tol=1.0):
        out = []
        for l in raw:
            for piece in clip_line(proj.line(l), CLIP_RECT):
                piece = dp_simplify(piece, tol)
                if line_len(piece) > 4:
                    out.append(piece)
        return out

    sc.water = polys("water")
    sc.parks = polys("parks")
    sc.forests = polys("forests", tol=1.5, min_area=4000)
    sc.rivers = [(r["name"], lines(r["lines"])) for r in geo.get("rivers", [])]
    sc.rails = lines(geo.get("rails", []), tol=1.5)
    sc.runways = lines(geo.get("runways", []))

    # ── улицы: не больше MAX_STREETS. Магистрали — по длине в кадре; остальные —
    # сначала те, что упомянуты в адресах точек, затем самые длинные рядом с маркерами.
    addr = " ".join(a.get("address", "") for a in data).lower()
    pts_xy = [proj.xy(a["lat"], a["lon"]) for a in data]
    cx = sum(p[0] for p in pts_xy) / len(pts_xy)
    cy = sum(p[1] for p in pts_xy) / len(pts_xy)
    core = (cx - 1100, cy - 1300, cx + 1100, cy + 1300)
    scored = []
    for s in geo.get("streets", []):
        pieces = lines(s["lines"])
        if not pieces:
            continue
        total = sum(line_len(p) for p in pieces)
        near = sum(line_len(c) for p in pieces for c in clip_line(p, core))
        if total < 150:
            continue
        key = short_name(s["name"])
        in_addr = bool(key) and key in addr
        scored.append((s["major"], in_addr, near, total, s["name"], pieces))
    majors = sorted((x for x in scored if x[0]), key=lambda x: -x[3])[:MAX_MAJOR_STREETS]
    minors = sorted((x for x in scored if not x[0]), key=lambda x: (not x[1], -(x[2] * 2 + x[3])))
    minors = minors[:MAX_STREETS - len(majors)]
    sc.streets_major = [(x[4], x[5]) for x in majors]
    sc.streets_minor = [(x[4], x[5]) for x in minors]

    # ── маркеры: истинные точки и разведённые позиции
    true_xy = {a["id"]: proj.xy(a["lat"], a["lon"]) for a in data}
    pos = spread_markers(true_xy)
    for a in data:
        a["true_xy"] = true_xy[a["id"]]
        a["xy"] = pos[a["id"]]

    # ── элементы оформления: их bbox — препятствия для подписей
    title = meta.get("title", "Сыктывкар")
    subtitle = meta.get("subtitle", "Туристическая карта")
    tw = max(typo.width(title, 96, True), typo.width(subtitle, 44), typo.width(dms(*CITY_CENTER), 26))
    sc.ui["title"] = Box(SAFE, SAFE, SAFE + tw + 2 * 56, SAFE + 300)
    sc.ui["north"] = Box(PAGE_W - SAFE - 200, SAFE, PAGE_W - SAFE, SAFE + 250)
    if LEGEND_MODE == "list":  # все точки по номерам — маркеры одного цвета, категории не различить
        items = [("num", a, a["name"]) for a in data] + [("yah", None, "Вы здесь")]
        size, row_h = 26, 46
    else:
        cats = [c for c in PALETTE if any(a["category"] == c for a in data)]
        cats += sorted({a["category"] for a in data} - set(cats))
        items = [("cat", c, c.capitalize()) for c in cats] + [("yah", None, "Вы здесь")]
        size, row_h = 30, 52
    col_w = 48 + min(560, max(typo.width(t, size) for _, _, t in items))
    rows = math.ceil(len(items) / 2)
    lw, lh = 2 * col_w + 3 * 44, 70 + row_h * rows + 40
    sc.ui["legend_items"] = (items, size, row_h, col_w)
    sc.ui["legend"] = Box(PAGE_W - SAFE - lw, PAGE_H - SAFE - lh, PAGE_W - SAFE, PAGE_H - SAFE)
    km = proj.scale * 1000
    sc.ui["scalebar"] = Box(SAFE, PAGE_H - SAFE - 190, SAFE + max(km + 150, 760), PAGE_H - SAFE)

    # ── «Вы здесь»
    yx, yy = proj.xy(*YOU_ARE_HERE)
    sc.yah = {"x": yx, "y": yy}

    # ── подписи достопримечательностей
    labels = []
    for a in data:
        lines_ = balanced_lines(a["name"], typo, LABEL_SIZE, LABEL_WRAP_W)
        w = max(typo.width(l, LABEL_SIZE) for l in lines_) + 2 * HALO_W
        h = len(lines_) * LABEL_LINE_H + 4
        x, y = a["xy"]
        labels.append(Label(a["id"], lines_, x, y, w, h))
    r = MARKER_R + MARKER_STROKE / 2
    marker_boxes = [Box(a["xy"][0] - r, a["xy"][1] - r, a["xy"][0] + r, a["xy"][1] + r) for a in data]
    yah_box = Box(yx - 24, yy - 24, yx + 24, yy + 24)
    ui_boxes = [b for k, b in sc.ui.items() if isinstance(b, Box)]
    obstacles = marker_boxes + [yah_box] + ui_boxes

    # «Указатель» — правый столбец под стрелкой севера. Сначала раскладываем без него;
    # если что-то не влезло — резервируем столбец и раскладываем заново.
    sc.labels = place_labels([Label(l.aid, l.lines, l.x, l.y, l.w, l.h) for l in labels], obstacles, SAFE_BOX)
    overflow = [l for l in sc.labels if not l.placed]
    if overflow:
        for _ in range(3):
            ibox = index_box(len(overflow), [a for a in data if a["id"] in {l.aid for l in overflow}], typo)
            sc.ui["index"] = ibox
            sc.labels = place_labels([Label(l.aid, l.lines, l.x, l.y, l.w, l.h) for l in labels],
                                     obstacles + [ibox], SAFE_BOX)
            new_overflow = [l for l in sc.labels if not l.placed]
            if len(new_overflow) == len(overflow):
                break
            overflow = new_overflow
        by_id = {a["id"]: a for a in data}
        sc.index = [by_id[l.aid] for l in sorted(overflow, key=lambda l: l.aid)]
        if not sc.index:
            sc.ui.pop("index", None)

    # «ВЫ ЗДЕСЬ» — подпись под точкой, иначе над, слева, справа
    yah_w = typo.width("ВЫ ЗДЕСЬ", 30, True) + 2 * HALO_W
    taken = obstacles + [l.box for l in sc.labels if l.placed] + ([sc.ui["index"]] if "index" in sc.ui else [])
    taken = [b for b in taken if b is not yah_box]
    for bx, by, anchor in ((yx - yah_w / 2, yy + 30, "middle"), (yx - yah_w / 2, yy - 30 - 40, "middle"),
                           (yx - 30 - yah_w, yy - 20, "end"), (yx + 30, yy - 20, "start")):
        box = Box(bx, by, bx + yah_w, by + 40)
        if not any(box.hits(o, 4) for o in taken):
            break
    sc.yah["box"] = box
    taken.append(box)

    # ── мультяшные рисунки объектов (как на референсе). Ставятся после подписей и до
    # районов: подписи важнее, а районы и реки потом обходят рисунки.
    if SHOW_ILLUSTRATIONS:
        sc.illustrations = place_illustrations(data, taken + [yah_box])
        taken += [il["core"] for il in sc.illustrations]

    # ── районы: границы и подписи
    sites = [proj.xy(lat, lon) for _, lat, lon in DISTRICTS]
    sc.district_edges = voronoi_edges(sites, BLEED_RECT)
    taken += marker_boxes + [yah_box]
    sc.district_labels = place_districts(proj, typo, taken)

    # ── подписи рек
    sc.river_labels = place_river_labels(sc, typo, taken)
    return sc


def find_illustration(a: dict) -> Path | None:
    if a.get("illustration"):
        p = ILLUSTRATIONS_DIR / a["illustration"]
        if p.is_file():
            return p
        warn(f"#{a['id']}: рисунок «{a['illustration']}» не найден в illustrations/")
    for p in sorted(ILLUSTRATIONS_DIR.glob(f"{a['id']:02d}-*")):
        if p.suffix.lower() in (".svg", ".png", ".webp"):
            return p
    return None


def load_illustration(p: Path, aid: int) -> dict:
    """SVG-рисунок встраивается в карту векторной группой (его можно править в
    редакторе), растровый — через <image>. viewBox нужен, чтобы вписать рисунок в квадрат."""
    if p.suffix.lower() != ".svg":
        with Image.open(p) as im:
            w, h, mime = im.width, im.height, Image.MIME.get(im.format, "image/png")
        return {"kind": "raster", "vb": [0, 0, w, h], "href": f"data:{mime};base64," + base64.b64encode(p.read_bytes()).decode()}
    root = ET.fromstring(p.read_text("utf-8"))
    vb = [float(v) for v in re.split(r"[\s,]+", (root.get("viewBox") or "0 0 200 200").strip())]
    parent = {c: e for e in root.iter() for c in e}
    for e in list(root.iter()):
        if e is not root and not e.tag.startswith(f"{{{SVG_NS}}}"):  # служебные теги Inkscape и т. п.
            parent[e].remove(e)
            continue
        e.tag = e.tag.split("}", 1)[-1]
        for k in [k for k in e.attrib if k.startswith("{")]:
            del e.attrib[k]
    body = "".join(ET.tostring(c, encoding="unicode") for c in root)
    # id внутри рисунков не должны столкнуться друг с другом на общей карте
    body = re.sub(r'(\bid="|url\(#|href="#)([^")]+)', lambda m: f"{m.group(1)}il{aid:02d}-{m.group(2)}", body)
    return {"kind": "svg", "vb": vb, "body": body}


def place_illustrations(data: list[dict], taken: list[Box]) -> list[dict]:
    """Рисунок встаёт прямо над своим номером, как на референсе. Если там занято —
    ближайшее свободное место по кольцам вокруг маркера (к номеру ведёт пунктирная выноска);
    не нашлось — пробуем рисунок поменьше; совсем нет места — WARN."""
    out = []
    r0 = MARKER_R + MARKER_STROKE / 2

    def crowd(a):
        return -sum(1 for b in data if b is not a and math.dist(a["xy"], b["xy"]) < 420)

    items = [(a, find_illustration(a)) for a in data]
    for a, p in sorted(((a, p) for a, p in items if p), key=lambda it: (crowd(it[0]), it[0]["id"])):
        il = load_illustration(p, a["id"])
        mx, my = a["xy"]
        found = None
        # близость к номеру важнее размера: сначала рядом (в том числе уменьшенный), потом дальше
        for lo, hi in ((0, 330), (330, ILLU_MAX_DIST)):
            for size in (ILLU_SIZE, ILLU_SIZE * 0.82, ILLU_SIZE * 0.68):
                k = size / max(il["vb"][2], il["vb"][3])
                w, h = il["vb"][2] * k, il["vb"][3] * k
                ix, iy = mx, my - r0 - 2 - h / 2 + h * 0.06  # низ рисунка (тень) касается номера
                cands = []
                for rad in range(lo, hi + 1, 30):
                    steps = 1 if rad == 0 else max(8, int(2 * math.pi * rad / 55))
                    for s in range(steps):
                        t = 2 * math.pi * s / steps
                        cx, cy = ix + rad * math.cos(t), iy + rad * math.sin(t)
                        cands.append((rad + (40 if cy > my else 0), cx, cy))
                cands.sort()
                for _, cx, cy in cands:
                    box = Box(cx - w / 2, cy - h / 2, cx + w / 2, cy + h / 2)
                    core = Box(box.x0 + w * 0.05, box.y0 + h * 0.03, box.x1 - w * 0.05, box.y1 - h * 0.05)
                    if box.inside(SAFE_BOX) and not any(core.hits(o, 4) for o in taken):
                        found = (box, core, k)
                        break
                if found:
                    break
            if found:
                break
        if not found:
            warn(f"#{a['id']}: рисунку не нашлось места на карте — пропущен")
            continue
        box, core, k = found
        taken.append(core)
        out.append({"id": a["id"], "xy": (mx, my), "box": box, "core": core, "scale": k, "il": il})

    # Выноски не должны перекрещиваться: если у двух рисунков одного размера выноски
    # пересекаются, меняем рисунки местами (суммарно выноски становятся короче).
    def leader_of(it):
        (mx, my), core = it["xy"], it["core"]
        nx, ny = min(max(mx, core.x0), core.x1), min(max(my, core.y0), core.y1)
        d = math.dist((mx, my), (nx, ny))
        if d - r0 <= 22:
            return None
        return [(mx + (nx - mx) * r0 / d, my + (ny - my) * r0 / d), (nx, ny)]

    def crosses(p, q):
        (a, b), (c, d) = p, q
        def side(o, x, y):
            return (x[0] - o[0]) * (y[1] - o[1]) - (x[1] - o[1]) * (y[0] - o[0])
        return side(a, b, c) * side(a, b, d) < 0 and side(c, d, a) * side(c, d, b) < 0

    for _ in range(3):
        swapped = False
        for i, p in enumerate(out):
            for q in out[i + 1:]:
                lp, lq = leader_of(p), leader_of(q)
                if lp and lq and crosses(lp, lq) and abs((p["box"].x1 - p["box"].x0) - (q["box"].x1 - q["box"].x0)) < 1:
                    for key in ("box", "core"):
                        p[key], q[key] = q[key], p[key]
                    swapped = True
        if not swapped:
            break
    for it in out:
        it["leader"] = leader_of(it)
    return out


def index_box(n: int, items: list[dict], typo: Typo) -> Box:
    x1 = PAGE_W - SAFE
    w = 480
    h = 80 + sum(16 + 34 * len(typo.wrap(a["name"], 28, w - 110, max_lines=3)) for a in items) + 24
    y0 = SAFE + 290
    return Box(x1 - w, y0, x1, y0 + h)


def place_districts(proj: Projection, typo: Typo, taken: list[Box]) -> list[dict]:
    out = []
    inner = Box(SAFE + 20, SAFE + 20, PAGE_W - SAFE - 20, PAGE_H - SAFE - 20)
    ccx, ccy = proj.xy(*CITY_CENTER)
    for name, lat, lon in DISTRICTS:
        if len(out) >= 8:
            break
        text = name.upper() if DISTRICT_CAPS else name
        w = typo.width(text, DISTRICT_SIZE, DISTRICT_BOLD, spacing=DISTRICT_SPACING) + 12
        h = 44
        x, y = proj.xy(lat, lon)
        if inner.x0 + w / 2 <= x <= inner.x1 - w / 2 and inner.y0 + h <= y <= inner.y1 - h:
            # внутри листа: ищем свободное место по спирали вокруг центра района
            for rad in range(0, 700, 60):
                steps = 1 if rad == 0 else 12
                for k in range(steps):
                    ang = 2 * math.pi * k / steps
                    bx = x + rad * math.cos(ang) - w / 2
                    by = y + rad * math.sin(ang) - h / 2
                    box = Box(bx, by, bx + w, by + h)
                    if box.inside(inner) and not any(box.hits(o, 10) for o in taken):
                        out.append({"name": text, "box": box, "edge": None})
                        taken.append(box)
                        break
                else:
                    continue
                break
            continue
        # за краем листа: подпись у края со стрелкой в сторону района и расстоянием
        dist_km = math.hypot((lat - CITY_CENTER[0]) * proj.mlat, (lon - CITY_CENTER[1]) * proj.mlon) / 1000
        text_full = f"{text}  {dist_km:.0f} км"
        w = typo.width(text_full, DISTRICT_SIZE, DISTRICT_BOLD, spacing=DISTRICT_SPACING * 0.6) + 12 + 50
        dx, dy = x - ccx, y - ccy
        ts = []
        if dx > 0:
            ts.append((inner.x1 - ccx) / dx)
        if dx < 0:
            ts.append((inner.x0 - ccx) / dx)
        if dy > 0:
            ts.append((inner.y1 - ccy) / dy)
        if dy < 0:
            ts.append((inner.y0 - ccy) / dy)
        t = min(ts)
        ex, ey = ccx + dx * t, ccy + dy * t
        bx = min(max(ex - w / 2, inner.x0), inner.x1 - w)
        by = min(max(ey - h / 2, inner.y0), inner.y1 - h)
        horizontal = abs(ey - inner.y0) < 1 or abs(ey - inner.y1) < 1
        angle = math.degrees(math.atan2(dy, dx))
        for off in [0] + [s * k for k in range(1, 14) for s in (1, -1)]:
            box = Box(bx, by, bx + w, by + h).moved(*((off * 90, 0) if horizontal else (0, off * 70)))
            if box.inside(inner) and not any(box.hits(o, 10) for o in taken):
                out.append({"name": text_full, "box": box, "edge": angle})
                taken.append(box)
                break
    if len(out) < 5:
        warn(f"подписей районов {len(out)} — меньше пяти (мешают маркеры и подписи)")
    return out


def place_river_labels(sc: Scene, typo: Typo, taken: list[Box]) -> list[dict]:
    out = []
    inner = Box(SAFE + 40, SAFE + 40, PAGE_W - SAFE - 40, PAGE_H - SAFE - 40)
    for name, lines_ in sc.rivers:
        if name not in ("Сысола", "Вычегда") or not lines_:
            continue
        text = f"р. {name}"
        w = typo.width(text, 34) + 10
        best = None
        for line in sorted(lines_, key=line_len, reverse=True):
            acc = 0.0
            for a, b in zip(line, line[1:]):
                seg = math.dist(a, b)
                acc += seg
                if seg < 1 or acc < 120:
                    continue
                acc = 0.0
                mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
                ang = math.degrees(math.atan2(b[1] - a[1], b[0] - a[0]))
                if ang > 90:
                    ang -= 180
                elif ang <= -90:
                    ang += 180
                if ang > 80:  # почти вертикальная река читается снизу вверх
                    ang -= 180
                ca, sa = abs(math.cos(math.radians(ang))), abs(math.sin(math.radians(ang)))
                bw, bh = w * ca + 40 * sa, w * sa + 40 * ca
                box = Box(mx - bw / 2, my - bh / 2, mx + bw / 2, my + bh / 2)
                if not box.inside(inner) or any(box.hits(o, 8) for o in taken):
                    continue
                score = abs(ang) / 2 + math.dist((mx, my), (PAGE_W / 2, PAGE_H / 2)) / 40
                if best is None or score < best[0]:
                    best = (score, {"name": text, "x": mx, "y": my, "angle": ang, "box": box})
        if best:
            out.append(best[1])
            taken.append(best[1]["box"])
    return out


def dms(lat: float, lon: float) -> str:
    def one(v):
        d = int(v)
        m = int((v - d) * 60)
        s = round(((v - d) * 60 - m) * 60)
        return f"{d}°{m:02d}′{s:02d}″"
    return f"{one(lat)} с. ш. · {one(lon)} в. д."


# ═══════════════════════════════ SVG ═══════════════════════════════

def d_line(pts) -> str:
    return "M" + "L".join(f"{fmt(x)} {fmt(y)}" for x, y in pts)


def d_rings(rings) -> str:
    return "".join(d_line(r) + "Z" for r in rings if len(r) >= 3)


def svg_text(x, y, s, size, *, bold=False, fill=None, anchor=None, spacing=None, italic=False,
             halo=False, halo_color=None, halo_w=HALO_W, line_h=None, extra=None) -> str:
    lines = s if isinstance(s, list) else [s]
    fill = fill or LABEL_TEXT          # константы читаются при вызове — их меняет use_style()
    halo_color = halo_color or LABEL_HALO
    a = {"x": x, "y": y, "font-family": FONT_STACK, "font-size": size,
         "font-weight": "bold" if bold else None, "font-style": "italic" if italic else None,
         "letter-spacing": spacing, "text-anchor": anchor, "fill": fill}
    if halo:
        a.update({"fill": halo_color, "stroke": halo_color, "stroke-width": 2 * halo_w,
                  "stroke-linejoin": "round", "class": "halo"})
    if extra:
        a.update(extra)
    if len(lines) == 1:
        body = escape(lines[0])
    else:
        body = "".join(el("tspan", {"x": x, "dy": 0 if i == 0 else line_h}, escape(l)) for i, l in enumerate(lines))
    return el("text", a, body)


def haloed(x, y, s, size, **kw) -> str:
    """Подпись с белым halo: две копии текста — обводка снизу, заливка сверху.
    paint-order короче, но cairosvg и Figma его не понимают."""
    return svg_text(x, y, s, size, halo=True, **kw) + svg_text(x, y, s, size, **kw)


def marker_glyph(x: float, y: float, r: float, fill: str, edge: str, stroke: float, cls: str | None = None) -> str:
    """Фигура маркера: круг (ТЗ) или скруглённый квадрат (референс)."""
    if MARKER_SHAPE == "square":
        return el("rect", {"class": cls, "x": x - r, "y": y - r, "width": 2 * r, "height": 2 * r, "rx": round(r * 0.18, 1),
                           "fill": fill, "stroke": edge, "stroke-width": stroke})
    return el("circle", {"class": cls, "cx": x, "cy": y, "r": r, "fill": fill, "stroke": edge, "stroke-width": stroke})


def layer(lid: str, title: str, children, web: bool) -> str:
    attrs = {"id": lid}
    if not web:
        attrs.update({"inkscape:groupmode": "layer", "inkscape:label": title})
    return el("g", attrs, children)


def render_svg(sc: Scene, typo: Typo, web: bool = False) -> str:
    proj, data = sc.proj, sc.data
    out = []

    # ── суша
    out.append(layer("land", "Суша", el("rect", {
        "x": BLEED_RECT[0], "y": BLEED_RECT[1], "width": PAGE_W + 2 * BLEED, "height": PAGE_H + 2 * BLEED,
        "fill": LAND}), web))

    # ── парки и леса
    parks = [el("path", {"d": d_rings(r), "fill": FOREST, "fill-rule": "evenodd"}) for r in sc.forests]
    parks += [el("path", {"d": d_rings(r), "fill": PARK, "fill-rule": "evenodd"}) for r in sc.parks]
    out.append(layer("parks", "Парки и леса", parks, web))

    # ── реки: осевые линии (видны там, где нет полигона), сверху полигоны воды
    rivers = []
    for name, lines_ in sc.rivers:
        for l in lines_:
            rivers.append(el("path", {"d": d_line(l), "fill": "none", "stroke": WATER, "stroke-width": 10,
                                      "stroke-linecap": "round", "stroke-linejoin": "round", "data-name": name or None}))
    # сначала обводки всех полигонов, потом заливки поверх — иначе на стыках соседних
    # полигонов OSM видны швы
    rivers += [el("path", {"d": d_rings(r), "fill": "none", "stroke": WATER_EDGE, "stroke-width": 3,
                           "stroke-linejoin": "round"}) for r in sc.water]
    rivers += [el("path", {"d": d_rings(r), "fill": WATER, "fill-rule": "evenodd", "stroke": WATER,
                           "stroke-width": 1.5, "stroke-linejoin": "round"}) for r in sc.water]
    for rl in sc.river_labels:
        rivers.append(svg_text(rl["x"], rl["y"] + 12, rl["name"], 34, italic=True, bold=RIVER_LABEL_BOLD,
                               fill=WATER_TEXT, anchor="middle", spacing=2, extra={"transform": f"rotate({fmt(rl['angle'])} {fmt(rl['x'])} {fmt(rl['y'])})"}))
    out.append(layer("rivers", "Реки", rivers, web))

    # ── районы: схематичные границы + подписи
    dist = []
    if DISTRICT_BOUNDARIES:
        dist.append(el("path", {"d": "".join(d_line([a, b]) for a, b in sc.district_edges), "fill": "none",
                                "stroke": DISTRICT_LINE, "stroke-width": 1.5, "stroke-dasharray": "12 9"}))
    for dl in sc.district_labels:
        b = dl["box"]
        under = DISTRICT_HALO or base_color_at(sc, b.cx, b.cy)  # по умолчанию halo в цвет подложки
        if dl["edge"] is None:
            dist.append(haloed(b.cx, b.y1 - 11, dl["name"], DISTRICT_SIZE, fill=DISTRICT_TEXT, anchor="middle",
                               bold=DISTRICT_BOLD, spacing=DISTRICT_SPACING or None, halo_color=under, halo_w=4))
        else:
            # треугольник-стрелка в сторону района; вершины считаем сами — rotate() на path
            # cairosvg отрисовывает неверно
            ax, ay = b.x0 + 22, b.cy
            t = math.radians(dl["edge"])
            ux, uy, px, py = math.cos(t), math.sin(t), -math.sin(t), math.cos(t)
            # стрелка с древком: (вдоль, поперёк) в локальных координатах
            shape = [(-20, -3.5), (4, -3.5), (4, -12), (22, 0), (4, 12), (4, 3.5), (-20, 3.5)]
            arrow = [(ax + u * ux + v * px, ay + u * uy + v * py) for u, v in shape]
            dist.append(el("path", {"d": d_line(arrow) + "Z", "fill": DISTRICT_TEXT}))
            dist.append(haloed(b.x0 + 54, b.y1 - 11, dl["name"], DISTRICT_SIZE, fill=DISTRICT_TEXT, bold=DISTRICT_BOLD,
                               spacing=DISTRICT_SPACING * 0.6 or None, halo_color=under, halo_w=4))
    districts_layer = layer("districts", "Районы", dist, web)  # кладётся поверх улиц

    # ── улицы: второстепенные, ж/д, ВПП, магистрали (сначала все окантовки, потом заливки)
    st = []
    for l in sc.runways:
        st.append(el("path", {"d": d_line(l), "fill": "none", "stroke": RUNWAY,
                              "stroke-width": max(10.0, 45 * proj.scale), "stroke-linecap": "butt"}))
    round_ = {"fill": "none", "stroke-linecap": "round", "stroke-linejoin": "round"}
    if STREET_MINOR_CASING_W:
        for name, ls in sc.streets_minor:
            st.append(el("path", {"d": "".join(d_line(l) for l in ls), **round_, "stroke": STREET_MINOR_CASING,
                                  "stroke-width": STREET_MINOR_CASING_W}))
    for name, ls in sc.streets_major:
        st.append(el("path", {"d": "".join(d_line(l) for l in ls), **round_, "stroke": STREET_MAJOR_CASING,
                              "stroke-width": STREET_MAJOR_CASING_W}))
    for name, ls in sc.streets_minor:
        st.append(el("path", {"d": "".join(d_line(l) for l in ls), **round_, "stroke": STREET_MINOR,
                              "stroke-width": STREET_MINOR_W, "data-name": name}))
    if sc.rails:
        st.append(el("path", {"d": "".join(d_line(l) for l in sc.rails), "fill": "none", "stroke": RAIL,
                              "stroke-width": 3, "stroke-dasharray": "16 10"}))
    for name, ls in sc.streets_major:
        st.append(el("path", {"d": "".join(d_line(l) for l in ls), **round_, "stroke": STREET_MAJOR,
                              "stroke-width": STREET_MAJOR_W, "data-name": name}))
    out.append(layer("streets", "Улицы", st, web))
    out.append(districts_layer)

    if sc.illustrations:
        ills = []
        for it in sc.illustrations:
            b, il = it["box"], it["il"]
            g = []
            if it["leader"]:  # пунктир из точек от номера к рисунку
                g.append(el("path", {"d": d_line(it["leader"]), "fill": "none", "stroke": LABEL_TEXT, "stroke-width": 4,
                                     "stroke-linecap": "round", "stroke-dasharray": "0.1 9", "stroke-opacity": 0.75}))
            vx, vy = il["vb"][0], il["vb"][1]
            tr = f"translate({fmt(b.x0)} {fmt(b.y0)}) scale({it['scale']:.4f})" + (
                f" translate({fmt(-vx)} {fmt(-vy)})" if vx or vy else "")
            body = il["body"] if il["kind"] == "svg" else el("image", {
                "href": il["href"], "xlink:href": il["href"], "width": il["vb"][2], "height": il["vb"][3]})
            g.append(el("g", {"transform": tr}, body))
            attrs = {"id": f"illustration-{it['id']:02d}", "data-id": it["id"]}
            if web:
                attrs.update({"class": "illu", "aria-hidden": "true"})
            ills.append(el("g", attrs, g))
        out.append(layer("illustrations", "Рисунки объектов", ills, web))

    # ── «Вы здесь» (в HTML — с пульсацией)
    yx, yy, yb = sc.yah["x"], sc.yah["y"], sc.yah["box"]
    yah = []
    if web:
        yah.append(el("circle", {"class": "yah-pulse", "cx": yx, "cy": yy, "r": 18, "fill": YAH_RED}))
    yah.append(el("circle", {"cx": yx, "cy": yy, "r": 18, "fill": YAH_RED, "stroke": "#FFFFFF", "stroke-width": 6}))
    anchor = "middle" if abs(yb.cx - yx) < 2 else ("end" if yb.x1 <= yx else "start")
    tx = yb.cx if anchor == "middle" else (yb.x1 - HALO_W if anchor == "end" else yb.x0 + HALO_W)
    yah.append(haloed(tx, yb.y1 - 10, "ВЫ ЗДЕСЬ", 30, bold=True, fill=YAH_RED, anchor=anchor))
    out.append(layer("you-are-here", "Вы здесь", yah, web))

    # ── маркеры
    mk = []
    dots: list[tuple[float, float]] = []
    for a in data:
        x, y = a["xy"]
        tx_, ty_ = a["true_xy"]
        c = a["color"]
        g = []
        if math.dist((x, y), (tx_, ty_)) > 6:  # маркер разведён — показываем истинную точку
            g.append(el("path", {"d": d_line([(tx_, ty_), (x, y)]), "stroke": LABEL_TEXT, "stroke-width": 3}))
            if not any(math.dist((tx_, ty_), d) < 24 for d in dots):  # у соседей по дому — одна общая точка
                dots.append((tx_, ty_))
                g.append(el("circle", {"cx": tx_, "cy": ty_, "r": 10, "fill": "#FFFFFF", "stroke": LABEL_TEXT, "stroke-width": 4}))
        fill = MARKER_FILL or c
        if web:
            g.append(el("circle", {"class": "hit", "cx": x, "cy": y, "r": 44, "fill": "transparent"}))
            g.append(marker_glyph(x, y, MARKER_R + 14, "none", MARKER_EDGE if MARKER_FILL else c, 6, cls="ring"))
        g.append(marker_glyph(x, y, MARKER_R, fill, MARKER_EDGE, MARKER_STROKE, cls="dot" if web else None))
        g.append(svg_text(x, y + 13, str(a["id"]), MARKER_NUM_SIZE, bold=True, fill=on_color(fill), anchor="middle",
                          extra={"pointer-events": "none"} if web else None))
        attrs = {"id": f"marker-{a['id']:02d}", "data-id": a["id"]}
        if web:
            attrs.update({"class": "marker", "data-x": fmt(x), "data-y": fmt(y), "tabindex": 0, "role": "button",
                          "aria-label": f"{a['id']}. {a['name']} — {a['category']}",
                          "style": f"--c:{fill};--hi:{brighter(fill)}"})
        mk.append(el("g", attrs, g))
    out.append(layer("markers", "Маркеры", mk, web))

    # ── подписи
    lb = []
    for lab in sc.labels:
        if not lab.placed:
            continue
        b = lab.box
        first = b.y0 + 2 + LABEL_LINE_H / 2 + LABEL_SIZE * 0.35
        if lab.side == "right":
            tx, anchor = b.x0 + HALO_W, None
        else:
            tx, anchor = b.x1 - HALO_W, "end"
        g = []
        if abs(lab.dy) > LABEL_LINE_H * 0.6:  # подпись далеко от маркера — короткая выноска
            ex = b.x0 if lab.side == "right" else b.x1
            d = math.dist((lab.x, lab.y), (ex, b.cy)) or 1
            r0 = MARKER_R + MARKER_STROKE / 2
            sx, sy = lab.x + (ex - lab.x) * r0 / d, lab.y + (b.cy - lab.y) * r0 / d
            g.append(el("path", {"d": d_line([(sx, sy), (ex, b.cy)]), "stroke": LABEL_TEXT,
                                 "stroke-width": 2, "stroke-opacity": 0.7}))
        g.append(haloed(tx, first, lab.lines, LABEL_SIZE, anchor=anchor, line_h=LABEL_LINE_H, italic=LABEL_ITALIC))
        lb.append(el("g", {"id": f"label-{lab.aid:02d}", "data-id": lab.aid}, g))
    out.append(layer("labels", "Подписи", lb, web))

    # ── заголовок
    tb = sc.ui["title"]
    title = sc.meta.get("title", "Сыктывкар")
    subtitle = sc.meta.get("subtitle", "Туристическая карта")
    out.append(layer("title", "Заголовок", [
        el("rect", {"x": tb.x0, "y": tb.y0, "width": tb.x1 - tb.x0, "height": tb.y1 - tb.y0, "rx": 28,
                    "fill": CARD, "fill-opacity": 0.94, "stroke": CARD_EDGE, "stroke-width": 2}),
        svg_text(tb.x0 + 56, tb.y0 + 130, title, 96, bold=True),
        svg_text(tb.x0 + 56, tb.y0 + 196, subtitle, 44),
        svg_text(tb.x0 + 56, tb.y0 + 252, dms(*CITY_CENTER), 26, fill=MUTED_TEXT),
    ], web))

    # ── стрелка севера
    nb = sc.ui["north"]
    ncx, top = nb.cx, nb.y0
    out.append(layer("north", "Север", [
        el("circle", {"cx": ncx, "cy": top + 125, "r": 100, "fill": CARD, "fill-opacity": 0.92, "stroke": CARD_EDGE, "stroke-width": 2}),
        el("path", {"d": f"M{fmt(ncx)} {fmt(top + 78)}L{fmt(ncx - 38)} {fmt(top + 205)}L{fmt(ncx)} {fmt(top + 175)}Z", "fill": LABEL_TEXT}),
        el("path", {"d": f"M{fmt(ncx)} {fmt(top + 78)}L{fmt(ncx + 38)} {fmt(top + 205)}L{fmt(ncx)} {fmt(top + 175)}Z",
                    "fill": "#FFFFFF", "stroke": LABEL_TEXT, "stroke-width": 3, "stroke-linejoin": "round"}),
        svg_text(ncx, top + 68, "С", 38, bold=True, anchor="middle"),
    ], web))

    # ── масштабная линейка 1 км
    sb = sc.ui["scalebar"]
    km = proj.scale * 1000
    x0, ybar = sb.x0 + 40, sb.y0 + 92
    segs = []
    for i in range(4):
        segs.append(el("rect", {"x": x0 + i * km / 4, "y": ybar, "width": km / 4, "height": 18,
                                "fill": LABEL_TEXT if i % 2 == 0 else "#FFFFFF", "stroke": LABEL_TEXT, "stroke-width": 2}))
    denom = 1_000_000 / (km / DPI * 25.4)
    denom = round(denom, -3) if denom > 10_000 else round(denom, -2)
    out.append(layer("scalebar", "Масштаб", [
        el("rect", {"x": sb.x0, "y": sb.y0, "width": sb.x1 - sb.x0, "height": sb.y1 - sb.y0, "rx": 20,
                    "fill": CARD, "fill-opacity": 0.94, "stroke": CARD_EDGE, "stroke-width": 2}),
        svg_text(x0, ybar - 18, "0", 28, anchor="middle"),
        svg_text(x0 + km / 2, ybar - 18, "500 м", 28, anchor="middle"),
        svg_text(x0 + km, ybar - 18, "1 км", 28, bold=True, anchor="middle"),
        *segs,
        svg_text(x0, ybar + 58, f"Масштаб 1 : {denom:,.0f}".replace(",", " "), 24, fill=MUTED_TEXT),
        svg_text(x0, ybar + 88, "Основа © участники OpenStreetMap (ODbL) · координаты ±200 м", 20, fill=MUTED_TEXT),
    ], web))

    # ── легенда категорий
    lg = sc.ui["legend"]
    items, size, row_h, col_w = sc.ui["legend_items"]
    rows = math.ceil(len(items) / 2)
    leg = [el("rect", {"x": lg.x0, "y": lg.y0, "width": lg.x1 - lg.x0, "height": lg.y1 - lg.y0, "rx": 24,
                       "fill": CARD, "fill-opacity": 0.95, "stroke": CARD_EDGE, "stroke-width": 2}),
           svg_text(lg.x0 + 44, lg.y0 + 62, "Обозначения" if LEGEND_MODE != "list" else "Достопримечательности", 34, bold=True)]
    for i, (kind, key, name) in enumerate(items):
        col, row = divmod(i, rows)
        ix = lg.x0 + 44 + col * (col_w + 44)
        iy = lg.y0 + 70 + row_h * (row + 1)
        cy = iy - size * 0.36
        if kind == "yah":
            leg.append(el("circle", {"cx": ix + 17, "cy": cy, "r": 12, "fill": YAH_RED, "stroke": "#FFFFFF", "stroke-width": 4}))
        elif kind == "cat":
            leg.append(el("circle", {"cx": ix + 17, "cy": cy, "r": 17, "fill": PALETTE.get(key, FALLBACK_COLOR),
                                     "stroke": "#FFFFFF", "stroke-width": 4}))
        else:
            fill = MARKER_FILL or key["color"]
            leg.append(marker_glyph(ix + 17, cy, 18, fill, MARKER_EDGE, 3))
            leg.append(svg_text(ix + 17, cy + 8, str(key["id"]), 22, bold=True, fill=on_color(fill), anchor="middle"))
        if typo.width(name, size) > col_w - 48:
            while name and typo.width(name + "…", size) > col_w - 48:
                name = name[:-1]
            name = name.rstrip() + "…"
        leg.append(svg_text(ix + 48, iy, name, size))
    out.append(layer("legend", "Легенда", leg, web))

    # ── «Указатель» для подписей, которые не уместились на карте
    if sc.index and "index" in sc.ui:
        ib = sc.ui["index"]
        ix = [el("rect", {"x": ib.x0, "y": ib.y0, "width": ib.x1 - ib.x0, "height": ib.y1 - ib.y0, "rx": 24,
                          "fill": CARD, "fill-opacity": 0.95, "stroke": CARD_EDGE, "stroke-width": 2}),
              svg_text(ib.x0 + 36, ib.y0 + 58, "Указатель", 34, bold=True)]
        y = ib.y0 + 96
        for a in sc.index:
            lines_ = typo.wrap(a["name"], 28, ib.x1 - ib.x0 - 110, max_lines=3)
            fill = MARKER_FILL or a["color"]
            ix.append(marker_glyph(ib.x0 + 60, y + 14, 24, fill, MARKER_EDGE, 4))
            ix.append(svg_text(ib.x0 + 60, y + 24, str(a["id"]), 26, bold=True, fill=on_color(fill), anchor="middle"))
            ix.append(svg_text(ib.x0 + 98, y + 24, lines_, 28, line_h=34))
            y += 16 + 34 * len(lines_)
        out.append(layer("index", "Указатель", ix, web))

    if not web:
        out.append(el("g", {"id": "guides", "inkscape:groupmode": "layer", "inkscape:label": "Направляющие (safe zone)",
                            "display": "none"}, [
            el("rect", {"x": SAFE, "y": SAFE, "width": PAGE_W - 2 * SAFE, "height": PAGE_H - 2 * SAFE,
                        "fill": "none", "stroke": "#FF00FF", "stroke-width": 2, "stroke-dasharray": "20 10"}),
        ]))

    root = {"xmlns": "http://www.w3.org/2000/svg", "viewBox": f"0 0 {PAGE_W} {PAGE_H}",
            "xmlns:xlink": "http://www.w3.org/1999/xlink" if any(i["il"]["kind"] == "raster" for i in sc.illustrations) else None}
    if web:
        root.update({"id": "map-svg", "preserveAspectRatio": "xMidYMid meet", "aria-labelledby": "map-svg-title"})
    else:
        root.update({"xmlns:inkscape": "http://www.inkscape.org/namespaces/inkscape",
                     "width": "210mm", "height": "297mm"})
    head = [el("title", {"id": "map-svg-title"} if web else None,
               escape(f"{sc.meta.get('title', 'Сыктывкар')} — {sc.meta.get('subtitle', 'Туристическая карта')}")),
            el("desc", None, escape(f"{len(data)} достопримечательностей. Основа © участники OpenStreetMap (ODbL)."))]
    svg = el("svg", root, head + out)
    return ('<?xml version="1.0" encoding="UTF-8"?>\n' + svg + "\n") if not web else svg


# ═══════════════════════════════ PNG / PDF ═══════════════════════════════

def ensure_cairo_env() -> None:
    """На macOS Homebrew-cairo лежит в /opt/homebrew/lib, куда dlopen по умолчанию не
    смотрит. Если cairosvg не импортируется, перезапускаемся с DYLD_FALLBACK_LIBRARY_PATH."""
    try:
        import cairosvg  # noqa: F401
        return
    except OSError:
        pass
    except ImportError:
        return
    if sys.platform == "darwin" and not os.environ.get("_SYKT_REEXEC"):
        for d in ("/opt/homebrew/lib", "/usr/local/lib"):
            if Path(d, "libcairo.2.dylib").exists():
                env = dict(os.environ, _SYKT_REEXEC="1",
                           DYLD_FALLBACK_LIBRARY_PATH=f"{d}:{os.environ.get('DYLD_FALLBACK_LIBRARY_PATH', '')}".rstrip(":"))
                os.execve(sys.executable, [sys.executable, *sys.argv], env)


def svg_for_raster(svg: str, typo: Typo) -> str:
    """cairosvg берёт только первое семейство из font-family. Если DejaVu Sans нет,
    подставляем найденный шрифт, иначе он молча падает на Helvetica без жирного."""
    if typo.family and typo.family != "DejaVu Sans":
        return svg.replace(f'font-family="{FONT_STACK}"', f'font-family="{typo.family}"')
    return svg


def export_png_pdf(svg: str, typo: Typo) -> tuple[bool, bool]:
    src = svg_for_raster(svg, typo)
    png_ok = pdf_ok = False
    try:
        import cairosvg
        png = cairosvg.svg2png(bytestring=src.encode("utf-8"), output_width=PAGE_W, output_height=PAGE_H,
                               background_color="white")
        Image.open(io.BytesIO(png)).convert("RGB").save(OUT_PNG, dpi=(DPI, DPI), optimize=True)
        png_ok = True
        cairosvg.svg2pdf(bytestring=src.encode("utf-8"), write_to=str(OUT_PDF))
        pdf_ok = True
    except (ImportError, OSError) as exc:
        resvg = shutil.which("resvg")
        if resvg:
            with tempfile.NamedTemporaryFile("w", suffix=".svg", delete=False, encoding="utf-8") as f:
                f.write(svg)
            subprocess.run([resvg, "--width", str(PAGE_W), "--height", str(PAGE_H), "--background", "white",
                            f.name, str(OUT_PNG)], check=True)
            os.unlink(f.name)
            Image.open(OUT_PNG).convert("RGB").save(OUT_PNG, dpi=(DPI, DPI), optimize=True)
            png_ok = True
            warn("cairosvg недоступен — PNG отрисован через resvg, PDF не создан")
        else:
            warn(f"PNG не создан: нет ни cairosvg ({exc}), ни resvg. pip install cairosvg (+ brew install cairo)")
    return png_ok, pdf_ok


def export_cmyk(profile: Path) -> Path | None:
    from PIL import ImageCms
    if not OUT_PNG.exists():
        warn(f"CMYK: нет {OUT_PNG.name}")
        return None
    out = OUT_PNG.with_name(OUT_PNG.stem + "_cmyk.tif")
    im = Image.open(OUT_PNG).convert("RGB")
    srgb = ImageCms.createProfile("sRGB")
    cmyk = ImageCms.getOpenProfile(str(profile))
    tr = ImageCms.buildTransform(srgb, cmyk, "RGB", "CMYK", renderingIntent=ImageCms.Intent.RELATIVE_COLORIMETRIC)
    ImageCms.applyTransform(im, tr).save(out, dpi=(DPI, DPI), compression="tiff_lzw",
                                         icc_profile=cmyk.tobytes())
    return out


# ═══════════════════════════════ фото и легенда ═══════════════════════════════

def find_photo(a: dict) -> Path | None:
    if a.get("photo"):
        p = PHOTOS_DIR / a["photo"]
        if p.is_file():
            return p
        warn(f"#{a['id']}: файл фото «{a['photo']}» не найден в photos/")
    for p in sorted(PHOTOS_DIR.glob(f"{a['id']:02d}*")):
        if p.suffix.lower() in IMG_EXT and not p.name[2:3].isdigit():
            return p
    return None


def apply_lut(im: Image.Image) -> Image.Image:
    for name, k in LUT:
        im = getattr(ImageEnhance, name)(im).enhance(k)
    return im


def placeholder(a: dict, typo: Typo) -> Image.Image:
    c = a["color"]
    im = Image.new("RGB", (THUMB, THUMB), mix(c, "#FFFFFF", 0.78))
    d = ImageDraw.Draw(im)
    for i in range(-THUMB, THUMB, 36):  # лёгкая штриховка — сразу видно, что это заглушка
        d.line([(i, 0), (i + THUMB, THUMB)], fill=mix(c, "#FFFFFF", 0.70), width=10)
    d.text((THUMB / 2, THUMB / 2), initials(a["name"]), font=typo.font(230, True), fill=mix(c, "#000000", 0.15),
           anchor="mm")
    return im


def drawing_thumb(a: dict, typo: Typo) -> Image.Image | None:
    """Рисунок объекта на светлом фоне цвета категории — замена фото в легенде и HTML."""
    p = find_illustration(a)
    if p is None:
        return None
    side = int(THUMB * 0.84)
    try:
        if p.suffix.lower() == ".svg":
            import cairosvg
            png = cairosvg.svg2png(bytestring=svg_for_raster(p.read_text("utf-8"), typo).encode("utf-8"),
                                   output_width=side, output_height=side)
            art = Image.open(io.BytesIO(png)).convert("RGBA")
        else:
            art = Image.open(p).convert("RGBA")
            art.thumbnail((side, side), Image.LANCZOS)
    except (ImportError, OSError) as exc:
        warn(f"#{a['id']}: рисунок не отрисовался ({exc})")
        return None
    im = Image.new("RGB", (THUMB, THUMB), mix(a["color"], "#FFFFFF", 0.82))
    im.paste(art, ((THUMB - art.width) // 2, (THUMB - art.height) // 2 + THUMB // 40), art)
    return im


def square_photos(data: list[dict], typo: Typo) -> dict[int, tuple[Image.Image, str]]:
    """id → (квадратная картинка 600×600, что это: "photo" | "drawing" | "placeholder")."""
    out = {}
    for a in data:
        p = find_photo(a)
        if p is None:
            drawing = drawing_thumb(a, typo)
            if drawing is not None:
                warn(f"#{a['id']} «{a['name']}»: нет фото — в легенде и HTML вместо него рисунок")
                out[a["id"]] = (drawing, "drawing")
            else:
                warn(f"#{a['id']} «{a['name']}»: нет фото — плейсхолдер с инициалами «{initials(a['name'])}»")
                out[a["id"]] = (placeholder(a, typo), "placeholder")
            continue
        im = ImageOps.exif_transpose(Image.open(p)).convert("RGB")
        im = ImageOps.fit(im, (THUMB, THUMB), Image.LANCZOS, centering=(0.5, 0.45))
        out[a["id"]] = (apply_lut(im), "photo")
    return out


def circle_badge(photo: Image.Image, d: int, ring: int = 8) -> Image.Image:
    """Круглая миниатюра с белой обводкой; маска рисуется в 4× для гладкого края."""
    full = d + 2 * ring
    ss = 4
    big = Image.new("RGBA", (full * ss, full * ss), (0, 0, 0, 0))
    m = Image.new("L", big.size, 0)
    ImageDraw.Draw(m).ellipse([0, 0, full * ss - 1, full * ss - 1], fill=255)
    big.paste((255, 255, 255, 255), (0, 0), m)
    inner = Image.new("L", (d * ss, d * ss), 0)
    ImageDraw.Draw(inner).ellipse([0, 0, d * ss - 1, d * ss - 1], fill=255)
    big.paste(photo.resize((d * ss, d * ss), Image.LANCZOS), (ring * ss, ring * ss), inner)
    return big.resize((full, full), Image.LANCZOS)


def render_legend(meta: dict, data: list[dict], photos: dict, typo: Typo) -> int:
    img = Image.new("RGB", (PAGE_W, PAGE_H), LEGEND_BG)
    draw = ImageDraw.Draw(img)
    title = f"{meta.get('title', 'Сыктывкар')} · достопримечательности"
    draw.text((SAFE, SAFE + 70), title, font=typo.font(68, True), fill=LABEL_TEXT, anchor="ls")
    draw.text((SAFE, SAFE + 128), "Номера совпадают с маркерами на карте", font=typo.font(36), fill=MUTED_TEXT, anchor="ls")

    cols = 2
    rows = max(7, math.ceil(len(data) / cols))
    top, bottom = SAFE + 190, PAGE_H - SAFE
    row_h = (bottom - top) / rows
    col_w = (PAGE_W - 2 * SAFE) / cols
    d = int(min(row_h - 40, 380))
    ring = 8
    drawn = 0
    for i, a in enumerate(data):
        col, row = divmod(i, rows)  # по колонкам: слева 1–7, справа 8–14
        x0 = SAFE + col * col_w
        y0 = top + row * row_h
        cy = y0 + row_h / 2
        badge = circle_badge(photos[a["id"]][0], d, ring)
        bx, by = int(x0 + 20), int(cy - badge.height / 2)
        shadow = Image.new("RGBA", (badge.width + 40, badge.height + 40), (0, 0, 0, 0))
        ImageDraw.Draw(shadow).ellipse([20, 26, 20 + badge.width, 26 + badge.height], fill=(60, 40, 10, 60))
        shadow = shadow.filter(ImageFilter.GaussianBlur(10))
        img.paste(shadow, (bx - 20, by - 20), shadow)
        img.paste(badge, (bx, by), badge)
        # номер в левом верхнем углу кружка
        r = badge.width / 2
        nx, ny = bx + r - r * 0.72, by + r - r * 0.72
        nr = 46
        fill = MARKER_FILL or a["color"]
        num = Image.new("RGBA", ((nr + 6) * 8, (nr + 6) * 8), (0, 0, 0, 0))
        nd = ImageDraw.Draw(num)
        outer, inner = [0, 0, num.width - 1, num.height - 1], [6 * 8, 6 * 8, num.width - 6 * 8 - 1, num.height - 6 * 8 - 1]
        if MARKER_SHAPE == "square":  # тот же вид номера, что на карте этого стиля
            nd.rounded_rectangle(outer, radius=10 * 8, fill=MARKER_EDGE)
            nd.rounded_rectangle(inner, radius=7 * 8, fill=fill)
        else:
            nd.ellipse(outer, fill="#FFFFFF")
            nd.ellipse(inner, fill=fill)
        num = num.resize((2 * (nr + 6), 2 * (nr + 6)), Image.LANCZOS)
        img.paste(num, (int(nx - nr - 6), int(ny - nr - 6)), num)
        draw.text((nx, ny + 2), str(a["id"]), font=typo.font(46, True), fill=on_color(fill), anchor="mm")
        # подпись
        tx = bx + badge.width + 44
        tw = x0 + col_w - tx - 30
        name_lines = typo.wrap(a["name"], 46, tw, bold=True, max_lines=3)
        block_h = len(name_lines) * 56 + 50
        ty = cy - block_h / 2 + 44
        for ln in name_lines:
            draw.text((tx, ty), ln, font=typo.font(46, True), fill=LABEL_TEXT, anchor="ls")
            ty += 56
        draw.ellipse([tx, ty - 8, tx + 22, ty + 14], fill=a["color"])
        draw.text((tx + 34, ty + 12), a["category"], font=typo.font(36), fill=MUTED_TEXT, anchor="ls")
        drawn += 1
    img.save(OUT_LEGEND, dpi=(DPI, DPI), optimize=True)
    return drawn


# ═══════════════════════════════ HTML ═══════════════════════════════

HTML_TEMPLATE = r"""<!doctype html>
<html lang="ru">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>__TITLE__</title>
<meta name="description" content="__DESCRIPTION__">
<meta name="theme-color" content="#F1E4C6">
<meta property="og:type" content="website">
<meta property="og:locale" content="ru_RU">
<meta property="og:title" content="__OG_TITLE__">
<meta property="og:description" content="__DESCRIPTION__">
<meta property="og:image" content="__OG_IMAGE__">
<meta property="og:image:width" content="2480">
<meta property="og:image:height" content="3508">
__OG_URL__<meta name="twitter:card" content="summary_large_image">
<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 64 64'%3E%3Ccircle cx='32' cy='32' r='26' fill='%23D32F2F' stroke='white' stroke-width='6'/%3E%3C/svg%3E">
<style>
:root{
  --bg:#FBF6EC; --paper:#FFFDF8; --sand:#F1E4C6; --map-bg:#E9D8B4;
  --ink:#2A2622; --muted:#5E5447; --line:#E2D2B2;
  --accent:#5C4033; --accent-hover:#47302A; --on-accent:#FFFFFF; --focus:#0B5CC2;
  --header-h:64px;
}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%;scroll-padding-top:calc(var(--header-h) + 12px)}
body{margin:0;background:var(--bg);color:var(--ink);
  font:16px/1.5 "DejaVu Sans",Verdana,"PT Sans",system-ui,-apple-system,"Segoe UI",Roboto,Arial,sans-serif}
.top{position:sticky;top:0;z-index:20;display:flex;align-items:center;justify-content:space-between;gap:12px;
  min-height:var(--header-h);padding:8px max(16px,env(safe-area-inset-right)) 8px max(16px,env(safe-area-inset-left));
  background:var(--sand);border-bottom:1px solid var(--line)}
.top h1{margin:0;font-size:clamp(16px,2.3vw,22px);line-height:1.25}
.top h1 span{font-weight:400;color:var(--muted)}
.btn{display:inline-flex;align-items:center;gap:8px;min-height:44px;padding:0 18px;border-radius:999px;
  background:var(--accent);color:var(--on-accent);font-weight:700;font-size:15px;text-decoration:none;white-space:nowrap}
.btn:hover{background:var(--accent-hover)}
.btn svg{width:18px;height:18px}
a:focus-visible,button:focus-visible,.marker:focus-visible{outline:3px solid var(--focus);outline-offset:2px}
.layout{display:grid;grid-template-columns:minmax(0,1.1fr) minmax(340px,1fr)}
.map-pane{position:sticky;top:var(--header-h);height:calc(100vh - var(--header-h));height:calc(100dvh - var(--header-h));
  background:var(--map-bg);overflow:hidden}
.map-pane svg{display:block;width:100%;height:100%;touch-action:pan-y;user-select:none;-webkit-user-select:none}
.map-pane svg.is-zoomed{touch-action:none;cursor:grab}
.map-pane svg.is-dragging{cursor:grabbing}
.map-tools{position:absolute;right:12px;bottom:12px;display:flex;flex-direction:column;gap:8px}
.map-tools button{width:44px;height:44px;border-radius:12px;border:1px solid var(--line);background:var(--paper);
  color:var(--ink);font:700 22px/1 inherit;cursor:pointer;box-shadow:0 1px 4px rgba(42,38,34,.18)}
.map-tools button:hover{background:#fff}
.list-pane{padding:20px 20px 32px}
.list-pane h2{margin:4px 0 4px;font-size:20px}
.list-pane .hint{margin:0 0 16px;color:var(--muted);font-size:14px}
.cards{list-style:none;margin:0;padding:0;display:grid;gap:12px}
.card{position:relative;display:grid;grid-template-columns:96px 1fr;gap:14px;align-items:start;padding:12px;
  background:var(--paper);border:2px solid var(--line);border-radius:16px;
  transition:border-color .25s ease,box-shadow .25s ease,background-color .25s ease}
.card:hover,.card.is-hover{border-color:var(--c)}
.card.is-active{border-color:var(--c);box-shadow:0 0 0 4px color-mix(in srgb,var(--c) 22%,transparent);
  background:color-mix(in srgb,var(--c) 6%,var(--paper))}
.card.flash{animation:flash .9s ease}
@keyframes flash{0%{box-shadow:0 0 0 0 var(--c)}100%{box-shadow:0 0 0 14px transparent}}
.card>div{min-width:0;overflow-wrap:break-word}
.thumb{width:96px;height:96px;border-radius:50%;object-fit:cover;border:4px solid #fff;box-shadow:0 0 0 2px var(--c)}
.head{display:flex;align-items:center;gap:8px}
.num{flex:none;display:inline-grid;place-items:center;min-width:30px;height:30px;padding:0 6px;border-radius:999px;
  background:var(--c-ink);color:#fff;font-weight:700;font-size:15px}
.card h3{margin:0;font-size:17px;line-height:1.3}
.cat{margin:4px 0 6px;font-size:14px;color:var(--muted)}
.cat i{display:inline-block;width:10px;height:10px;margin-right:6px;border-radius:50%;background:var(--c)}
.desc{margin:0 0 6px;font-size:15px}
.addr{margin:0;font-size:14px;color:var(--muted)}
.card-hit{position:absolute;inset:0;width:100%;border:0;padding:0;border-radius:14px;background:transparent;cursor:pointer}
footer{padding:16px 20px 28px;border-top:1px solid var(--line);color:var(--muted);font-size:13px}
footer a{color:inherit}
.sr-only{position:absolute;width:1px;height:1px;margin:-1px;overflow:hidden;clip:rect(0 0 0 0);white-space:nowrap}
/* SVG-карта */
.marker{cursor:pointer;outline:none}
.marker .dot{transition:stroke-width .2s ease,fill .2s ease}
.marker:hover .dot,.marker.is-hover .dot,.marker:focus-visible .dot,.marker.is-active .dot{stroke-width:8;fill:var(--hi)}
.marker .ring{opacity:0;transition:opacity .2s ease}
.marker.is-active .ring,.marker:focus-visible .ring{opacity:1}
.hit{fill:transparent}
.illu{cursor:pointer}
.yah-pulse{transform-box:fill-box;transform-origin:center;animation:yah 1.8s ease-out infinite;pointer-events:none}
@keyframes yah{0%{transform:scale(1);opacity:.55}100%{transform:scale(3.4);opacity:0}}
@media (max-width:860px){
  .layout{grid-template-columns:minmax(0,1fr)}
  .map-pane{position:relative;top:auto;height:auto;aspect-ratio:2480/3508}
  .list-pane{padding:16px}
  .top .btn span{display:none}
}
@media (prefers-reduced-motion:reduce){
  .yah-pulse{animation:none;opacity:.3}
  *,*::before,*::after{transition:none!important;animation-duration:0s!important;scroll-behavior:auto!important}
}
</style>
</head>
<body>
<header class="top">
  <h1>__CITY__ · <span>__SUBTITLE__</span></h1>
  __PDF_BUTTON__
</header>
<main class="layout">
  <section class="map-pane" id="map" aria-label="Карта">
    __SVG__
    <div class="map-tools" role="group" aria-label="Масштаб карты">
      <button type="button" data-zoom="in" aria-label="Приблизить">+</button>
      <button type="button" data-zoom="out" aria-label="Отдалить">−</button>
      <button type="button" data-zoom="reset" aria-label="Показать всю карту">⤢</button>
    </div>
  </section>
  <aside class="list-pane" aria-labelledby="list-title">
    <h2 id="list-title">Достопримечательности</h2>
    <p class="hint">Нажмите на точку на карте или на карточку — карта приблизится к месту.</p>
    <ol class="cards">
__CARDS__
    </ol>
  </aside>
</main>
<footer>Картографическая основа © <a href="https://www.openstreetmap.org/copyright">участники OpenStreetMap</a> (ODbL). Координаты приблизительные, ±200 м. Сгенерировано __DATE__.</footer>
<p class="sr-only" aria-live="polite" id="announce"></p>
<script type="application/json" id="attractions-data">__JSON__</script>
<script>
(() => {
  "use strict";
  const svg = document.getElementById("map-svg");
  if (!svg) return;
  const pane = document.getElementById("map");
  const FULL = {x: 0, y: 0, w: __PAGE_W__, h: __PAGE_H__};
  const reduce = matchMedia("(prefers-reduced-motion: reduce)").matches;
  const data = JSON.parse(document.getElementById("attractions-data").textContent);
  const byId = new Map(data.map(a => [String(a.id), a]));
  const markers = new Map(), cards = new Map();
  svg.querySelectorAll(".marker").forEach(g => markers.set(g.dataset.id, g));
  document.querySelectorAll(".card").forEach(c => cards.set(c.dataset.id, c));
  const announce = document.getElementById("announce");
  let vb = {...FULL}, anim = 0, active = null;

  const clamp = v => {
    const w = Math.min(Math.max(v.w, FULL.w / 10), FULL.w), h = w * FULL.h / FULL.w;
    return {x: Math.min(Math.max(v.x, 0), FULL.w - w), y: Math.min(Math.max(v.y, 0), FULL.h - h), w, h};
  };
  const scale = () => { const r = svg.getBoundingClientRect(); return Math.min(r.width / vb.w, r.height / vb.h) || 1; };
  function sizeHits() {  // зона нажатия маркера — не меньше 44×44 px на экране
    const r = Math.max(44, 22 / scale());
    svg.querySelectorAll(".hit").forEach(c => c.setAttribute("r", r.toFixed(1)));
  }
  function apply(v) {
    vb = v;
    svg.setAttribute("viewBox", `${v.x.toFixed(1)} ${v.y.toFixed(1)} ${v.w.toFixed(1)} ${v.h.toFixed(1)}`);
    svg.classList.toggle("is-zoomed", v.w < FULL.w - 1);
    sizeHits();
  }
  const ease = t => t < .5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
  function animateTo(target, ms = 600) {
    const t = clamp(target);
    cancelAnimationFrame(anim);
    if (reduce) return apply(t);
    const s = {...vb}, t0 = performance.now();
    const step = now => {
      const k = Math.min(1, (now - t0) / ms), e = ease(k);
      apply({x: s.x + (t.x - s.x) * e, y: s.y + (t.y - s.y) * e, w: s.w + (t.w - s.w) * e, h: s.h + (t.h - s.h) * e});
      if (k < 1) anim = requestAnimationFrame(step);
    };
    anim = requestAnimationFrame(step);
  }
  const zoomAround = (px, py, f) =>
    animateTo({x: px - (px - vb.x) / f, y: py - (py - vb.y) / f, w: vb.w / f, h: vb.h / f}, 350);
  const focusOn = (x, y, z = 3) => { const w = FULL.w / z, h = FULL.h / z; animateTo({x: x - w / 2, y: y - h / 2, w, h}); };
  function toSvg(cx, cy) {
    const p = svg.createSVGPoint(); p.x = cx; p.y = cy;
    return p.matrixTransform(svg.getScreenCTM().inverse());
  }
  function nearest(p) {  // ближайший маркер в пределах зоны нажатия — работает и при перекрытии зон
    let best = null, bd = Infinity;
    markers.forEach((g, id) => {
      const d = Math.hypot(+g.dataset.x - p.x, +g.dataset.y - p.y);
      if (d < bd) { bd = d; best = id; }
    });
    return bd <= Math.max(48, 26 / scale()) ? best : null;
  }
  function select(id, from) {
    if (active) { markers.get(active)?.classList.remove("is-active"); cards.get(active)?.classList.remove("is-active"); }
    active = id;
    const g = markers.get(id), c = cards.get(id);
    if (!g || !c) return;
    g.classList.add("is-active"); c.classList.add("is-active");
    g.parentNode.appendChild(g);  // поднять над соседями
    const a = byId.get(id);
    if (a) announce.textContent = `Выбрано: ${a.id}. ${a.name}, ${a.category}`;
    if (from === "map") {
      c.scrollIntoView({behavior: reduce ? "auto" : "smooth", block: "center"});
      c.classList.remove("flash"); void c.offsetWidth; c.classList.add("flash");
    } else {
      const r = pane.getBoundingClientRect();
      if (r.bottom < 120 || r.top > innerHeight - 120) pane.scrollIntoView({behavior: reduce ? "auto" : "smooth", block: "start"});
      focusOn(+g.dataset.x, +g.dataset.y);
    }
    history.replaceState(null, "", "#p" + id);
  }

  // клики и тапы по карте
  let drag = null, moved = false;
  const ptrs = new Map();
  svg.addEventListener("pointerdown", e => {
    ptrs.set(e.pointerId, {x: e.clientX, y: e.clientY});
    if (ptrs.size === 1) { drag = {x: e.clientX, y: e.clientY, vb: {...vb}}; moved = false; }
    else if (ptrs.size === 2) {
      const [a, b] = [...ptrs.values()];
      drag = {pinch: Math.hypot(a.x - b.x, a.y - b.y), vb: {...vb}, mid: toSvg((a.x + b.x) / 2, (a.y + b.y) / 2)};
      moved = true;
    }
  });
  svg.addEventListener("pointermove", e => {
    if (!ptrs.has(e.pointerId) || !drag) return;
    ptrs.set(e.pointerId, {x: e.clientX, y: e.clientY});
    if (drag.pinch && ptrs.size === 2) {
      const [a, b] = [...ptrs.values()], f = Math.hypot(a.x - b.x, a.y - b.y) / drag.pinch, m = drag.mid;
      cancelAnimationFrame(anim);
      apply(clamp({x: m.x - (m.x - drag.vb.x) / f, y: m.y - (m.y - drag.vb.y) / f, w: drag.vb.w / f, h: drag.vb.h / f}));
      return;
    }
    if (vb.w >= FULL.w - 1 && e.pointerType === "touch") return;  // не приближено — пусть скроллится страница
    const dx = e.clientX - drag.x, dy = e.clientY - drag.y;
    if (!moved && Math.hypot(dx, dy) < 6) return;
    if (!moved) { moved = true; svg.setPointerCapture(e.pointerId); svg.classList.add("is-dragging"); }
    const k = scale();
    cancelAnimationFrame(anim);
    apply(clamp({...drag.vb, x: drag.vb.x - dx / k, y: drag.vb.y - dy / k}));
  });
  const up = e => {
    ptrs.delete(e.pointerId);
    if (!ptrs.size) { drag = null; svg.classList.remove("is-dragging"); }
  };
  svg.addEventListener("pointerup", up);
  svg.addEventListener("pointercancel", up);
  svg.addEventListener("click", e => {
    if (moved) { moved = false; return; }
    const ill = e.target.closest(".illu");  // клик по рисунку объекта — как по его номеру
    if (ill) return select(ill.dataset.id, "map");
    const p = toSvg(e.clientX, e.clientY), id = nearest(p);
    if (id) select(id, "map");
  });
  svg.querySelectorAll(".illu").forEach(g => {
    const id = g.dataset.id;
    g.addEventListener("pointerenter", () => { markers.get(id)?.classList.add("is-hover"); cards.get(id)?.classList.add("is-hover"); });
    g.addEventListener("pointerleave", () => { markers.get(id)?.classList.remove("is-hover"); cards.get(id)?.classList.remove("is-hover"); });
  });
  svg.addEventListener("dblclick", e => { const p = toSvg(e.clientX, e.clientY); zoomAround(p.x, p.y, 2); });
  svg.addEventListener("wheel", e => {
    e.preventDefault();
    const p = toSvg(e.clientX, e.clientY);
    const f = Math.exp(-e.deltaY * (e.ctrlKey ? 0.01 : 0.0025));
    cancelAnimationFrame(anim);
    apply(clamp({x: p.x - (p.x - vb.x) / f, y: p.y - (p.y - vb.y) / f, w: vb.w / f, h: vb.h / f}));
  }, {passive: false});
  markers.forEach((g, id) => {
    g.addEventListener("keydown", e => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); select(id, "map"); } });
    g.addEventListener("pointerenter", () => cards.get(id)?.classList.add("is-hover"));
    g.addEventListener("pointerleave", () => cards.get(id)?.classList.remove("is-hover"));
  });
  cards.forEach((c, id) => {
    c.querySelector(".card-hit").addEventListener("click", () => select(id, "list"));
    c.addEventListener("pointerenter", () => markers.get(id)?.classList.add("is-hover"));
    c.addEventListener("pointerleave", () => markers.get(id)?.classList.remove("is-hover"));
  });
  document.querySelectorAll("[data-zoom]").forEach(b => b.addEventListener("click", () => {
    const cx = vb.x + vb.w / 2, cy = vb.y + vb.h / 2;
    if (b.dataset.zoom === "in") zoomAround(cx, cy, 1.6);
    else if (b.dataset.zoom === "out") zoomAround(cx, cy, 1 / 1.6);
    else animateTo(FULL);
  }));
  document.addEventListener("keydown", e => { if (e.key === "Escape") animateTo(FULL); });
  addEventListener("resize", sizeHits);
  sizeHits();
  const m = location.hash.match(/^#p(\d+)$/);
  if (m && markers.has(m[1])) select(m[1], "list");
})();
</script>
</body>
</html>
"""


def thumb_data_uri(im: Image.Image, size: int = 240) -> str:
    buf = io.BytesIO()
    im.resize((size, size), Image.LANCZOS).save(buf, "JPEG", quality=80, optimize=True, progressive=True)
    return "data:image/jpeg;base64," + base64.b64encode(buf.getvalue()).decode()


def render_html(sc: Scene, svg_web: str, photos: dict, pdf_href: str | None) -> str:
    meta, data = sc.meta, sc.data
    city = meta.get("title", "Сыктывкар")
    subtitle = meta.get("subtitle", "Туристическая карта")
    cards = []
    for a in data:
        c = a["color"]
        im, kind = photos[a["id"]]
        alt = {"photo": a["name"], "drawing": f"Рисунок: {a['name']}"}.get(kind, f"Фото пока нет: {a['name']}")
        cards.append(f"""      <li class="card" id="card-{a['id']}" data-id="{a['id']}" style="--c:{c};--c-ink:{deepen(c)}">
        <img class="thumb" src="{thumb_data_uri(im)}" alt="{html.escape(alt)}" width="96" height="96" decoding="async">
        <div>
          <div class="head"><span class="num" aria-hidden="true">{a['id']}</span><h3>{html.escape(a['name'])}</h3></div>
          <p class="cat"><i aria-hidden="true"></i>{html.escape(a['category'])}</p>
          <p class="desc">{html.escape(a.get('description', ''))}</p>
          <p class="addr">{html.escape(a.get('address', ''))}</p>
        </div>
        <button type="button" class="card-hit" aria-label="Показать на карте: {a['id']}. {html.escape(a['name'])}"></button>
      </li>""")
    payload = [{"id": a["id"], "name": a["name"], "category": a["category"], "address": a.get("address", ""),
                "lat": round(a["lat"], 5), "lon": round(a["lon"], 5),
                "x": round(a["xy"][0], 1), "y": round(a["xy"][1], 1)} for a in data]
    descr = (f"Туристическая карта Сыктывкара: {len(data)} достопримечательностей — панно, арт-объекты, "
             f"памятники, театр, собор и кафе. Фото, описания и адреса.")
    pdf_button = ""
    if pdf_href:
        pdf_button = (f'<a class="btn" href="{html.escape(pdf_href)}" download>'
                      '<svg viewBox="0 0 24 24" aria-hidden="true"><path fill="currentColor" d="M12 3a1 1 0 0 1 1 1v9.6l3.3-3.3 1.4 1.4L12 17.4 6.3 11.7l1.4-1.4L11 13.6V4a1 1 0 0 1 1-1zM5 19h14v2H5z"/></svg>'
                      '<span>Скачать PDF</span></a>')
    og_image = f"{SITE_URL}{OUT_PNG.name}"
    og_url = f'<meta property="og:url" content="{html.escape(SITE_URL)}">\n' if SITE_URL else ""
    rep = {
        "__TITLE__": html.escape(f"{city} · {subtitle} — {len(data)} достопримечательностей"),
        "__OG_TITLE__": html.escape(f"{city} · {subtitle}"),
        "__DESCRIPTION__": html.escape(descr),
        "__OG_IMAGE__": html.escape(og_image),
        "__OG_URL__": og_url,
        "__CITY__": html.escape(city),
        "__SUBTITLE__": html.escape(subtitle),
        "__PDF_BUTTON__": pdf_button,
        "__SVG__": svg_web,
        "__CARDS__": "\n".join(cards),
        "__DATE__": dt.date.today().strftime("%d.%m.%Y"),
        "__JSON__": json.dumps(payload, ensure_ascii=False).replace("</", "<\\/"),
        "__PAGE_W__": str(PAGE_W),
        "__PAGE_H__": str(PAGE_H),
    }
    out = HTML_TEMPLATE
    for k, v in rep.items():
        out = out.replace(k, v)
    return out


# ═══════════════════════════════ самопроверка ═══════════════════════════════

def base_color_at(sc: Scene, x: float, y: float) -> str:
    for rings in sc.water:
        if point_in_rings(x, y, rings):
            return WATER
    for rings in sc.parks:
        if point_in_rings(x, y, rings):
            return PARK
    for rings in sc.forests:
        if point_in_rings(x, y, rings):
            return FOREST
    return LAND


def label_contrasts(sc: Scene) -> tuple[list[float], list[float]]:
    """Худший контраст текста к подложке в пяти точках bbox (без учёта halo, т. е. с запасом)."""
    def worst(box, color):
        pts = [(box.cx, box.cy), (box.x0 + 8, box.y0 + 8), (box.x1 - 8, box.y0 + 8), (box.x0 + 8, box.y1 - 8), (box.x1 - 8, box.y1 - 8)]
        return min(contrast(color, base_color_at(sc, x, y)) for x, y in pts)
    attr = [worst(l.box, LABEL_TEXT) for l in sc.labels if l.placed]
    dist = [worst(d["box"], DISTRICT_TEXT) for d in sc.district_labels]
    return attr, dist


def html_theme_contrast() -> list[tuple[str, float]]:
    pairs = [("текст / фон", "#2A2622", "#FBF6EC"), ("текст / карточка", "#2A2622", "#FFFDF8"),
             ("вторичный / карточка", "#5E5447", "#FFFDF8"), ("вторичный / шапка", "#5E5447", "#F1E4C6"),
             ("кнопка", "#FFFFFF", "#5C4033")]
    pairs += [(f"номер «{k}»", "#FFFFFF", deepen(v)) for k, v in PALETTE.items()]
    return [(n, contrast(a, b)) for n, a, b in pairs]


def kb(p: Path) -> str:
    if not p.exists():
        return "—"
    s = p.stat().st_size
    return f"{s / 1024 / 1024:.2f} МБ" if s > 1024 * 1024 else f"{s / 1024:.0f} КБ"


def self_check(sc: Scene, svg_print: str, html_text: str, legend_count: int, png_ok: bool, pdf_ok: bool) -> None:
    ns = "{http://www.w3.org/2000/svg}"
    root = ET.fromstring(svg_print.split("?>", 1)[1])
    on_map = sum(1 for g in root.iter(f"{ns}g") if (g.get("id") or "").startswith("marker-"))
    m = re.search(r'<svg[^>]*id="map-svg"[\s\S]*?</svg>', html_text)
    html_markers = len(re.findall(r'class="marker"', m.group(0))) if m else 0
    html_cards = len(re.findall(r'<li class="card"', html_text))
    n = len(sc.data)
    attr_c, dist_c = label_contrasts(sc)
    shifted = sum(1 for l in sc.labels if l.shifted)
    spread = sum(1 for a in sc.data if math.dist(a["xy"], a["true_xy"]) > 6)
    streets = len(sc.streets_major) + len(sc.streets_minor)

    print("\n══════════════════ самопроверка ══════════════════")
    ok = lambda b: "OK " if b else "ERR"
    print(f"{ok(on_map == n)} точек в JSON: {n} · на карте (SVG): {on_map} · в легенде: {legend_count} · "
          f"в HTML: {html_cards} карточек / {html_markers} маркеров")
    if not (on_map == legend_count == html_cards == html_markers == n):
        warn("число точек в артефактах расходится с JSON")
    print(f"    подписи: на карте {sum(l.placed for l in sc.labels)}, сдвинуто {shifted}, "
          f"вынесено в «Указатель» {len(sc.index)}" + (f" ({', '.join(str(a['id']) for a in sc.index)})" if sc.index else ""))
    print(f"    маркеров разведено с выноской к точке: {spread}")
    print(f"    улиц: {streets} (магистралей {len(sc.streets_major)}, второстепенных {len(sc.streets_minor)}; лимит {MAX_STREETS})"
          + ("" if sc.has_geo else " — подложки нет"))
    print(f"    подписей районов: {len(sc.district_labels)} ({', '.join(d['name'].split('  ')[0].title() for d in sc.district_labels)})")
    print(f"    реки подписаны: {', '.join(r['name'] for r in sc.river_labels) or 'нет'}")
    if SHOW_ILLUSTRATIONS:
        have = sum(1 for a in sc.data if find_illustration(a))
        lead = sum(1 for i in sc.illustrations if i["leader"])
        small = sum(1 for i in sc.illustrations if i["box"].x1 - i["box"].x0 < ILLU_SIZE * 0.9)
        print(f"{ok(len(sc.illustrations) == have)} рисунков на карте: {len(sc.illustrations)} из {have} "
              f"(с выноской {lead}, уменьшено {small})")
    if attr_c:
        avg, mn = sum(attr_c) / len(attr_c), min(attr_c)
        print(f"{ok(mn >= 4.5)} контраст подписей к подложке: средний {avg:.1f}:1, минимум {mn:.1f}:1 "
              f"(к halo — {contrast(LABEL_TEXT, LABEL_HALO):.1f}:1)")
        if mn < 4.5:
            warn("есть подписи с контрастом ниже 4.5:1")
    if dist_c:
        avg, mn = sum(dist_c) / len(dist_c), min(dist_c)
        print(f"{ok(mn >= 4.5)} контраст подписей районов: средний {avg:.1f}:1, минимум {mn:.1f}:1")
        if mn < 4.5:
            warn("подписи районов ниже 4.5:1 — затемните DISTRICT_TEXT")
    worst = min(html_theme_contrast(), key=lambda x: x[1])
    print(f"{ok(worst[1] >= 4.5)} контраст текста в HTML: минимум {worst[1]:.1f}:1 ({worst[0]})")
    print(f"    файлы: SVG {kb(OUT_SVG)} · PNG {kb(OUT_PNG) if png_ok else 'не создан'} · легенда {kb(OUT_LEGEND)} · "
          f"HTML {kb(OUT_HTML)}" + (f" · PDF {kb(OUT_PDF)}" if pdf_ok else ""))
    if WARNINGS:
        print(f"    предупреждений: {len(WARNINGS)} (см. WARN выше)")


# ═══════════════════════════════ main ═══════════════════════════════

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--refresh-geo", action="store_true", help="перекачать подложку из OpenStreetMap (Overpass API)")
    ap.add_argument("--osm-raw", nargs="+", metavar="JSON", help=argparse.SUPPRESS)  # собрать кеш из сохранённых ответов Overpass
    ap.add_argument("--cmyk", metavar="ICC", type=Path, help="дополнительно сохранить CMYK-TIFF с этим ICC-профилем")
    ap.add_argument("--style", choices=[*STYLES, "both"], default="both",
                    help="tz — по ТЗ, ref — как на референсе (файлы *_ref), both — оба (по умолчанию)")
    args = ap.parse_args()

    ensure_cairo_env()
    meta, data = load_attractions()
    typo = Typo()
    geo = load_geo(args)
    photos = square_photos(data, typo)

    for style in (list(STYLES) if args.style == "both" else [args.style]):
        use_style(style)
        print(f"\n────────────── стиль «{style}» → {OUT_SVG.stem}.* ──────────────")
        sc = build_scene(meta, data, geo, typo)

        svg_print = render_svg(sc, typo, web=False)
        OUT_SVG.write_text(svg_print, "utf-8")
        png_ok, pdf_ok = export_png_pdf(svg_print, typo)
        legend_count = render_legend(meta, data, photos, typo)

        pdf_href = BOOKLET_PDF.name if BOOKLET_PDF.exists() else (OUT_PDF.name if pdf_ok else None)
        html_text = render_html(sc, render_svg(sc, typo, web=True), photos, pdf_href)
        OUT_HTML.write_text(html_text, "utf-8")

        if args.cmyk:
            out = export_cmyk(args.cmyk)
            if out:
                print(f"CMYK  {out.name} ({kb(out)})")

        self_check(sc, svg_print, html_text, legend_count, png_ok, pdf_ok)


if __name__ == "__main__":
    main()
