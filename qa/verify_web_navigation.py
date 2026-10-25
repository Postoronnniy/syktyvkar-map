"""Verify that the web-only update preserves artwork and remains self-contained."""
import contextlib
import io
import base64
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from web_navigation import navigation_script, update_page, house_labels


def map_svg(source):
    return re.search(r'<svg\b[^>]*\bid="map-svg".*?</svg>', source, re.S).group(0)


class NavigationBuildTests(unittest.TestCase):
    def test_artwork_text_and_existing_photos_are_preserved(self):
        for name in ("index.html", "index_tz.html"):
            old = subprocess.check_output(["git", "show", f"HEAD:{name}"], cwd=ROOT).decode("utf-8")
            new = (ROOT / name).read_text("utf-8")
            self.assertEqual(map_svg(old), map_svg(new))
            pattern = r'<script type="application/json" id="attractions-data">.*?</script>'
            self.assertEqual(re.findall(pattern, old, re.S), re.findall(pattern, new, re.S))
            old_cards = re.findall(r'<li class="card".*?</li>', old, re.S)
            new_cards = re.findall(r'<li class="card".*?</li>', new, re.S)
            self.assertEqual(len(old_cards), len(new_cards))
            for before, after in zip(old_cards, new_cards):
                self.assertEqual(re.sub(r'<img\b[^>]*>', '', before), re.sub(r'<img\b[^>]*>', '', after))
                if 'class="thumb illustrated"' not in after:
                    self.assertEqual(before, after)

    def test_all_missing_photos_use_their_own_embedded_drawing(self):
        data = json.loads((ROOT / "attractions.json").read_text("utf-8"))["attractions"]
        for name in ("index.html", "index_tz.html"):
            source = (ROOT / name).read_text("utf-8")
            for a in data:
                if a.get("photo"):
                    continue
                card = re.search(rf'<li class="card" id="card-{a["id"]}".*?</li>', source, re.S)[0]
                uri = re.search(r'data:image/svg\+xml;base64,([^"]+)', card)[1]
                self.assertEqual(base64.b64decode(uri), (ROOT / "illustrations" / a["illustration"]).read_bytes())
            self.assertEqual(source.count('class="thumb illustrated"'), 7)

    def test_house_labels_are_geographic_and_identical_in_both_styles(self):
        houses = [house_labels((ROOT / name).read_text("utf-8")) for name in ("index.html", "index_tz.html")]
        self.assertEqual(houses[0], houses[1])
        self.assertEqual(len(houses[0]), 10)
        self.assertEqual({h["number"] for h in houses[0] if h["street"] == "Коммунистическая улица"}, {"35", "37", "39", "43", "45", "47"})
        for h in houses[0]:
            self.assertTrue(0 < h["x"] < 2480 and 0 < h["y"] < 3508)
        # These two attractions share a house; show its number only once, at
        # its real footprint, not at either deliberately displaced map marker.
        kuratova = [h for h in houses[0] if h["street"] == "улица Куратова"]
        self.assertEqual(len(kuratova), 1)
        self.assertLess(abs(kuratova[0]["x"] - 1489.7), 5)
        self.assertLess(abs(kuratova[0]["y"] - 2268.5), 5)

    def test_embed_matches_source_and_is_idempotent(self):
        for name in ("index.html", "index_tz.html"):
            with tempfile.TemporaryDirectory(dir=ROOT / "qa", prefix=".navigation-test-") as tmp:
                self.assertTrue(Path(tmp).resolve().is_relative_to((ROOT / "qa").resolve()))
                p = Path(tmp) / name
                p.write_text((ROOT / name).read_text("utf-8"), "utf-8")
                with contextlib.redirect_stdout(io.StringIO()):
                    update_page(p)
                    once = p.read_text("utf-8")
                    update_page(p)
                self.assertEqual(once, p.read_text("utf-8"))
                self.assertEqual(once.count('id="callout-help"'), 1)
                self.assertEqual(once.count('id="navigation-data"'), 1)
                self.assertEqual(once.count('/* navigation:start */'), 1)
                self.assertNotRegex(once, r"__[A-Z_]+__")
                self.assertNotRegex(once, r'<script\b[^>]*\bsrc=')
                values = re.search(r"SYM_PX = ([\d.]+), PX_PER_M = ([\d.]+)", once).groups()
                self.assertIn(navigation_script(*map(float, values)), once)

    def test_generator_embeds_navigation_and_keeps_published_style(self):
        import generate_map as gen
        scene = SimpleNamespace(meta={}, data=[], proj=SimpleNamespace(scale=.25))
        for style, filename in (("tz", "index_tz.html"), ("ref", "index.html")):
            gen.use_style(style)
            self.assertEqual(gen.OUT_HTML.name, filename)
            result = gen.render_html(scene, '<svg id="map-svg"></svg>', {}, None)
            self.assertIn(navigation_script(gen.WEB_SYMBOL_MAX_SCALE, .25), result)
            self.assertIn('id="callout-help"', result)
            self.assertNotRegex(result, r"__[A-Z_]+__")


if __name__ == "__main__":
    unittest.main(verbosity=2)
