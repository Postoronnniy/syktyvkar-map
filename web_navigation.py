"""Embed navigation assets without rebuilding the cartographic artwork.

Run ``python web_navigation.py`` after editing map_navigation.js/css to update
the checked-in HTML pages. generate_map.py uses the same assets for new builds.
"""
from pathlib import Path
import base64
import html
import json
import re
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parent
NAVIGATION_HELP = ('<p class="hint navigation-hint" id="callout-help">'
    'При приближении миниатюры подвигаются к точкам, если рядом свободно. Их можно перетаскивать. '
    'Выберите рисунок: −/+ меняют размер, ↺ возвращает автоматическое размещение. '
    'С клавиатуры: стрелки — перемещение, +/− — размер, 0 — сброс. '
    'Кнопка ⤢ возвращает всю карту и исходное расположение рисунков.</p>')


def navigation_script(symbol_scale: float, px_per_m: float) -> str:
    return ((ROOT / "map_navigation.js").read_text("utf-8")
            .replace("__SYM_PX__", str(symbol_scale))
            .replace("__PX_PER_M__", f"{px_per_m:.5f}"))


def navigation_css() -> str:
    return ("/* navigation:start */\n" + (ROOT / "map_navigation.css").read_text("utf-8")
            + "/* navigation:end */")


def illustrated_cards(source: str) -> str:
    """Embed the original vector drawings; no Cairo dependency or network request."""
    data = json.loads((ROOT / "attractions.json").read_text("utf-8"))["attractions"]
    for a in data:
        if a.get("photo") or not a.get("illustration"):
            continue
        drawing = ROOT / "illustrations" / a["illustration"]
        if not drawing.is_file():
            continue
        uri = "data:image/svg+xml;base64," + base64.b64encode(drawing.read_bytes()).decode("ascii")
        tag = (f'<img class="thumb illustrated" src="{uri}" '
               f'alt="Рисунок: {html.escape(a["name"])}" width="96" height="96" decoding="async">')
        pattern = rf'(<li\b[^>]*\bid="card-{a["id"]}"[^>]*>\s*)<img\b[^>]*>'
        source = re.sub(pattern, lambda m: m[1] + tag, source)
    return source


def house_labels(source: str) -> list[dict]:
    """Project cached OSM addresses using the SVG's actual geographic anchors.

    The existing map uses an affine local projection. Fitting its rounded anchors
    keeps labels aligned in both themes without rebuilding or reflowing artwork.
    Only buildings explicitly named in attraction addresses are labelled.
    """
    payload = re.search(r'<script type="application/json" id="attractions-data">(.*?)</script>', source, re.S)
    svg_match = re.search(r'<svg\b[^>]*\bid="map-svg".*?</svg>', source, re.S)
    if not payload or not svg_match:
        return []
    data = json.loads(payload[1])
    anchors = {e.get("data-id"): e for e in ET.fromstring(svg_match[0]).iter()
               if "marker" in e.get("class", "").split()}
    pairs = [(a, anchors[str(a["id"])]) for a in data if str(a["id"]) in anchors]
    if len(pairs) < 2:
        return []

    def fit(geo, axis):
        coords = [(a[geo], float(e.get(axis))) for a, e in pairs]
        mx = sum(p[0] for p in coords) / len(coords)
        my = sum(p[1] for p in coords) / len(coords)
        variance = sum((x - mx) ** 2 for x, _ in coords)
        if not variance:
            raise ValueError("Cannot recover map projection from geographic anchors")
        slope = sum((x - mx) * (y - my) for x, y in coords) / variance
        if max(abs(my + (x - mx) * slope - y) for x, y in coords) > .5:
            raise ValueError("Map anchors do not match the address projection")
        return lambda value: my + (value - mx) * slope

    px, py = fit("lon", "data-ax"), fit("lat", "data-ay")
    def street_key(value):
        return re.sub(r"\b(?:улица|ул)\b\.?", "", value.lower()).strip()

    wanted = [(a.get("address", "").lower(), set(re.findall(r"\d+[а-яa-z]?(?:/\d+)?", a.get("address", "").lower())))
              for a in data]
    raw_path = ROOT / "geo" / "syktyvkar_buildings_raw.json"
    if not raw_path.is_file():
        return []
    raw = json.loads(raw_path.read_text("utf-8"))
    elements = raw if isinstance(raw, list) else raw.get("elements", [])
    houses, seen = [], set()
    for e in elements:
        tags = e.get("tags", {})
        number, street = tags.get("addr:housenumber", ""), tags.get("addr:street", "")
        if not number or not street or not any(street_key(street) in addr and number.lower() in nums for addr, nums in wanted):
            continue
        ring = e.get("geometry", [])
        if len(ring) < 3:
            continue
        # Place the label inside the footprint, including concave buildings:
        # intersect a scanline through its middle and use the longest interior span.
        yy = (min(p["lat"] for p in ring) + max(p["lat"] for p in ring)) / 2
        crossings = []
        for p, q in zip(ring, ring[1:] + ring[:1]):
            if (p["lat"] > yy) != (q["lat"] > yy):
                crossings.append(p["lon"] + (yy - p["lat"]) * (q["lon"] - p["lon"]) / (q["lat"] - p["lat"]))
        crossings.sort()
        spans = list(zip(crossings[::2], crossings[1::2]))
        if not spans:
            continue
        left, right = max(spans, key=lambda p: p[1] - p[0])
        x, y = px((left + right) / 2), py(yy)
        key = (street, number, round(x), round(y))
        if 0 < x < 2480 and 0 < y < 3508 and key not in seen:
            houses.append(dict(number=number, street=street, x=round(x, 2), y=round(y, 2)))
            seen.add(key)
    return sorted(houses, key=lambda a: (a["street"], a["number"], a["x"]))


def enhance_page(source: str) -> str:
    source = illustrated_cards(source)
    source = re.sub(r'<script type="application/json" id="navigation-data">.*?</script>\s*', '', source, flags=re.S)
    payload = json.dumps({"houses": house_labels(source)}, ensure_ascii=False).replace("</", "<\\/")
    return source.replace('<script type="application/json" id="attractions-data">',
                          f'<script type="application/json" id="navigation-data">{payload}</script>\n'
                          '<script type="application/json" id="attractions-data">', 1)


def update_page(path: Path) -> None:
    original = path.read_text("utf-8")
    settings = re.search(r"\bSYM_PX\s*=\s*([\d.]+),\s*PX_PER_M\s*=\s*([\d.]+)", original)
    if not settings:
        raise ValueError(f"{path.name}: navigation scale constants not found")
    script = navigation_script(*map(float, settings.groups()))
    updated, count = re.subn(r"<script>(?=\s*(?:\(\(\) => \{|// Geometry)).*?</script>",
                             lambda _: "<script>\n" + script + "</script>", original, flags=re.S)
    if count != 1:
        raise ValueError(f"{path.name}: expected one navigation script, got {count}")
    updated = re.sub(r"/\* navigation:start \*/.*?/\* navigation:end \*/\s*", "", updated, flags=re.S)
    updated = updated.replace("</style>", navigation_css() + "\n</style>", 1)
    updated = re.sub(r'<p class="hint navigation-hint" id="callout-help">.*?</p>\s*', "", updated, flags=re.S)
    updated = updated.replace('<ol class="cards">', NAVIGATION_HELP + '\n<ol class="cards">', 1)
    with path.open("w", encoding="utf-8", newline="\n") as output:
        output.write(enhance_page(updated))
    print(f"Updated {path.name} (map artwork preserved)")


if __name__ == "__main__":
    for name in ("index.html", "index_tz.html", "index_ref.html"):
        path = ROOT / name
        if path.exists():
            update_page(path)
