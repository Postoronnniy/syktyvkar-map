// Geometry is shared by the browser and the small dependency-free regression tests.
const CalloutGeometry = (() => {
  const overlaps = (a, b, gap = 0) => Math.abs(a.x - b.x) < (a.w + b.w) / 2 + gap
    && Math.abs(a.y - b.y) < (a.h + b.h) / 2 + gap;
  const inside = (p, b, pad) => p.x - p.w / 2 >= b.x + pad && p.x + p.w / 2 <= b.x + b.w - pad
    && p.y - p.h / 2 >= b.y + pad && p.y + p.h / 2 <= b.y + b.h - pad;
  function leader(marker, box, radius, square) {
    const end = {x: Math.min(Math.max(marker.x, box.x - box.w / 2), box.x + box.w / 2),
      y: Math.min(Math.max(marker.y, box.y - box.h / 2), box.y + box.h / 2)};
    const dx = end.x - marker.x, dy = end.y - marker.y, d = Math.hypot(dx, dy);
    if (!d) return null;
    const t = radius / (square ? Math.max(Math.abs(dx), Math.abs(dy)) : d);
    if (t >= 1) return null;
    return {start: {x: marker.x + dx * t, y: marker.y + dy * t}, end, length: d * (1 - t)};
  }
  const cross = (a, b, c) => (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
  function intersects(a, b) {
    // Shared endpoints are not crossings. Collinear overlap still counts.
    const [p, q, r, s] = [a.start, a.end, b.start, b.end], eps = 1e-7;
    if ([p, q].some(v => [r, s].some(w => Math.hypot(v.x - w.x, v.y - w.y) < eps))) return false;
    const c1 = cross(p, q, r), c2 = cross(p, q, s), c3 = cross(r, s, p), c4 = cross(r, s, q);
    if ([c1, c2, c3, c4].every(c => Math.abs(c) < eps)) {
      const key = Math.abs(q.x - p.x) > Math.abs(q.y - p.y) ? "x" : "y";
      return Math.min(Math.max(p[key], q[key]), Math.max(r[key], s[key]))
        - Math.max(Math.min(p[key], q[key]), Math.min(r[key], s[key])) > eps;
    }
    return c1 * c2 <= 0 && c3 * c4 <= 0;
  }
  function throughBox(line, box, gap = 0) {
    let lo = 0, hi = 1;
    for (const [axis, size] of [["x", "w"], ["y", "h"]]) {
      const min = box[axis] - box[size] / 2 - gap + 1e-6;
      const max = box[axis] + box[size] / 2 + gap - 1e-6;
      const delta = line.end[axis] - line.start[axis];
      if (Math.abs(delta) < 1e-9) {
        if (line.start[axis] < min || line.start[axis] > max) return false;
      } else {
        const a = (min - line.start[axis]) / delta, b = (max - line.start[axis]) / delta;
        lo = Math.max(lo, Math.min(a, b)); hi = Math.min(hi, Math.max(a, b));
      }
      if (lo >= hi) return false;
    }
    return hi > 0 && lo < 1;
  }
  const segments = points => points.slice(1).map((end, i) => ({start: points[i], end}));
  function labelCandidates(points, width, step) {
    const lengths = [0];
    for (let i = 1; i < points.length; i++) lengths.push(lengths[i - 1] + Math.hypot(points[i].x - points[i - 1].x, points[i].y - points[i - 1].y));
    const total = lengths[lengths.length - 1], half = width / 2;
    if (total < width) return [];
    const at = distance => {
      let i = 1; while (i < lengths.length - 1 && lengths[i] < distance) i++;
      const t = (distance - lengths[i - 1]) / (lengths[i] - lengths[i - 1] || 1);
      return {x: points[i - 1].x + (points[i].x - points[i - 1].x) * t,
        y: points[i - 1].y + (points[i].y - points[i - 1].y) * t};
    };
    const candidates = [];
    for (let d = half; d <= total - half; d += step) {
      const a = at(d - half), b = at(d + half), p = at(d), length = Math.hypot(b.x - a.x, b.y - a.y);
      // Labels can span consecutive straight pieces, but not a sharp bend.
      if (length < width * .97 || Math.abs(cross(a, b, p)) / length > step * .12) continue;
      let angle = Math.atan2(b.y - a.y, b.x - a.x) * 180 / Math.PI;
      if (angle > 90) angle -= 180; if (angle < -90) angle += 180;
      candidates.push({...p, angle});
    }
    return candidates;
  }
  function route(line, obstacles, otherLines, gap, bounds) {
    if (!line) return [];
    const {start, end} = line;
    const cost = points => segments(points).reduce((sum, s) => sum + Math.hypot(s.end.x - s.start.x, s.end.y - s.start.y)
      + obstacles.filter(b => throughBox(s, b)).length * gap * 1000
      + otherLines.filter(l => intersects(s, l)).length * gap * 300, (points.length - 2) * gap * 2);
    let best = [start, end], score = cost(best);
    // Keep straight lines unless a collision actually needs a detour.
    if (!obstacles.some(b => throughBox(line, b)) && !otherLines.some(l => intersects(line, l))) return best;
    const waypoints = [];
    const blocks = obstacles.filter(b => throughBox(line, b, gap));
    for (const b of blocks) for (const dx of [-1, 1]) for (const dy of [-1, 1])
      waypoints.push({x: b.x + dx * (b.w / 2 + gap), y: b.y + dy * (b.h / 2 + gap)});
    for (const l of otherLines.filter(l => intersects(line, l))) for (const p of [l.start, l.end])
      for (const [dx, dy] of [[-1, -1], [-1, 1], [1, -1], [1, 1]]) waypoints.push({x: p.x + dx * gap, y: p.y + dy * gap});
    const safe = waypoints.filter(p => !bounds || inside({...p, w: 0, h: 0}, bounds, 0)).slice(0, 28);
    const consider = points => {
      const value = cost(points);
      if (value < score) { best = points; score = value; }
    };
    for (const a of safe) {
      consider([start, a, end]);
      for (const b of safe) if (a !== b) consider([start, a, b, end]);
    }
    return best;
  }
  function near(marker, original, radius, obstacles, bounds, gap, otherLines = [], square = false) {
    const initialDistance = Math.hypot(original.x - marker.x, original.y - marker.y);
    const lineCost = p => {
      const l = leader(marker, p, radius, square);
      if (!l) return 0;
      return otherLines.filter(s => intersects(l, s)).length * gap * 120
        + obstacles.filter(b => !overlaps({...marker, w: 0, h: 0}, b) && throughBox(l, b)).length * gap * 180;
    };
    let best = original, score = initialDistance + lineCost(original);
    for (const extra of [0, gap * 2, gap * 4]) {
      for (const [dx, dy] of [[0, -1], [-1, -1], [1, -1], [-1, 0], [1, 0], [0, 1], [-1, 1], [1, 1]]) {
        const p = {...original,
          x: marker.x + dx * (radius + original.w / 2 + gap + extra),
          y: marker.y + dy * (radius + original.h / 2 + gap + extra)};
        const distance = Math.hypot(p.x - marker.x, p.y - marker.y);
        if (distance >= initialDistance - gap) continue;
        const cost = distance + .08 * Math.hypot(p.x - original.x, p.y - original.y) + lineCost(p);
        if (cost >= score - gap || !inside(p, bounds, gap) || obstacles.some(o => overlaps(p, o, gap))) continue;
        best = p; score = cost;
      }
    }
    return best;
  }
  return {overlaps, inside, leader, near, intersects, throughBox, route, segments, labelCandidates};
})();
if (typeof module !== "undefined" && module.exports) module.exports = CalloutGeometry;
if (typeof document !== "undefined") (() => {
  "use strict";
  const svg = document.getElementById("map-svg");
  if (!svg) return;
  const pane = document.getElementById("map");
  const initial = svg.viewBox.baseVal;
  const FULL = {x: initial.x, y: initial.y, w: initial.width, h: initial.height};
  const reduce = matchMedia("(prefers-reduced-motion: reduce)").matches;
  const SYM_PX = __SYM_PX__, PX_PER_M = __PX_PER_M__;
  const NS = "http://www.w3.org/2000/svg";
  const byId = new Map(JSON.parse(document.getElementById("attractions-data").textContent)
    .map(a => [String(a.id), a]));
  const markers = new Map([...svg.querySelectorAll(".marker")].map(g => [g.dataset.id, g]));
  const cards = new Map([...document.querySelectorAll(".card")].map(g => [g.dataset.id, g]));
  const syms = [...svg.querySelectorAll(".sym:not(.illu)")]
    .map(g => ({g, ax: +g.dataset.ax, ay: +g.dataset.ay}));
  const hits = [...svg.querySelectorAll(".marker .hit")];
  const announce = document.getElementById("announce");
  const dynScale = document.getElementById("dyn-scale");
  const limit = (n, lo, hi) => Math.min(Math.max(n, lo), hi);
  let vb = {...FULL}, symK = 1, anim = 0, active = null, editing = null;
  const mobile = matchMedia("(max-width: 860px)");
  const sheet = document.createElement("section");
  sheet.className = "place-sheet";
  sheet.hidden = true;
  sheet.setAttribute("aria-labelledby", "place-sheet-title");
  sheet.innerHTML = '<div class="sheet-summary"><img class="thumb" width="64" height="64" alt="">'
    + '<div><h2 id="place-sheet-title"></h2><p class="sheet-category"></p></div>'
    + '<button type="button" class="sheet-close" aria-label="Закрыть карточку места">×</button></div>'
    + '<p class="sheet-address"></p><div id="place-sheet-details" hidden><p class="sheet-description"></p></div>'
    + '<button type="button" class="sheet-toggle" aria-expanded="false" aria-controls="place-sheet-details">Подробнее</button>';
  document.body.appendChild(sheet);
  const sheetDetails = sheet.querySelector("#place-sheet-details"), sheetToggle = sheet.querySelector(".sheet-toggle");
  let sheetTrigger = null;
  function showSheet(id) {
    if (!mobile.matches) return;
    const card = cards.get(id), photo = card.querySelector(".thumb");
    sheetTrigger = markers.get(id);
    sheet.dataset.id = id;
    sheet.style.cssText = card.getAttribute("style");
    const img = sheet.querySelector("img");
    img.src = photo.src; img.alt = photo.alt; img.className = photo.className;
    sheet.querySelector("h2").textContent = `${id}. ${byId.get(id).name}`;
    sheet.querySelector(".sheet-category").textContent = card.querySelector(".cat").textContent;
    sheet.querySelector(".sheet-address").textContent = card.querySelector(".addr").textContent;
    sheet.querySelector(".sheet-description").textContent = card.querySelector(".desc").textContent;
    sheetDetails.hidden = true; sheetToggle.setAttribute("aria-expanded", "false"); sheetToggle.textContent = "Подробнее";
    sheet.hidden = false;
    positionMapTools();
  }
  function closeSheet(restoreFocus = false) {
    sheet.hidden = true;
    positionMapTools();
    if (restoreFocus) sheetTrigger?.focus({preventScroll: true});
    layoutCallouts(scale());
  }
  sheet.querySelector(".sheet-close").addEventListener("click", () => closeSheet(true));
  sheetToggle.addEventListener("click", () => {
    sheetDetails.hidden = !sheetDetails.hidden;
    sheetToggle.setAttribute("aria-expanded", String(!sheetDetails.hidden));
    sheetToggle.textContent = sheetDetails.hidden ? "Подробнее" : "Свернуть";
    positionMapTools();
    if (active) focusOn(active);
  });
  mobile.addEventListener("change", () => {
    if (!mobile.matches) closeSheet();
    apply(clamp(vb));
  });

  // A leader is in map coordinates; the drawing has its own translation and scale.
  // Keep the source artwork and its original overview placement intact.
  const callouts = new Map();
  const illustrationLayer = svg.querySelector("#illustrations");
  if (illustrationLayer) {
    const leaderLayer = document.createElementNS(NS, "g");
    leaderLayer.id = "callout-leaders";
    leaderLayer.setAttribute("aria-hidden", "true");
    illustrationLayer.before(leaderLayer);
    illustrationLayer.querySelectorAll(".illu").forEach(g => {
      const original = [...g.children].find(e => e.tagName.toLowerCase() === "path");
      const leader = original || document.createElementNS(NS, "path");
      const originalD = original?.getAttribute("d");
      leaderLayer.appendChild(leader);
      const box = g.getBBox();
      const hit = document.createElementNS(NS, "rect");
      Object.entries({"class": "illu-hit", x: box.x, y: box.y, width: box.width, height: box.height})
        .forEach(([key, value]) => hit.setAttribute(key, value));
      g.prepend(hit);
      const marker = markers.get(g.dataset.id), dot = marker.querySelector(".dot");
      const square = dot.tagName.toLowerCase() === "rect";
      const radius = +(dot.getAttribute(square ? "width" : "r")) / (square ? 2 : 1)
        + +(dot.getAttribute("stroke-width") || 0) / 2;
      const color = original?.getAttribute("stroke") || svg.querySelector("#labels text:not(.halo)")?.getAttribute("fill") || "#231F1B";
      const attrs = {"class": "callout-leader", "data-id": g.dataset.id, "fill": "none",
        "stroke": color, "stroke-width": 4, "stroke-linecap": "round",
        "stroke-dasharray": "0.1 9", "stroke-opacity": .75};
      Object.entries(attrs).forEach(([key, value]) => leader.setAttribute(key, value));
      g.removeAttribute("aria-hidden");
      g.setAttribute("tabindex", "0");
      g.setAttribute("role", "button");
      g.setAttribute("aria-label", `Миниатюра ${g.dataset.id}. ${byId.get(g.dataset.id)?.name || ""}`);
      g.setAttribute("aria-describedby", "callout-help");
      const title = document.createElementNS(NS, "title");
      title.textContent = "Перетащите рисунок. Shift + колесо — размер; двойной щелчок — вернуть.";
      g.prepend(title);
      callouts.set(g.dataset.id, {g, leader, originalD, marker, square, radius,
        ax: +g.dataset.ax, ay: +g.dataset.ay,
        cx: box.x + box.width / 2, cy: box.y + box.height / 2,
        width: box.width, height: box.height, dx: 0, dy: 0, size: 1,
        manual: false, autoX: 0, autoY: 0});
    });
  }

  const toolbar = document.createElement("div");
  toolbar.className = "map-tools callout-tools";
  toolbar.hidden = true;
  toolbar.setAttribute("role", "group");
  toolbar.setAttribute("aria-label", "Размер выбранной миниатюры");
  toolbar.innerHTML = '<span></span><button type="button" data-size="smaller" aria-label="Уменьшить миниатюру">−</button>'
    + '<button type="button" data-size="larger" aria-label="Увеличить миниатюру">+</button>'
    + '<button type="button" data-size="reset" aria-label="Сбросить размер и включить автоматическое размещение миниатюры">↺</button>';
  pane.appendChild(toolbar);
  const labelBoxes = [...svg.querySelectorAll("#labels .sym, #you-are-here .sym")].map(g => {
    const b = g.getBBox();
    return {ax: +g.dataset.ax, ay: +g.dataset.ay,
      x: b.x + b.width / 2, y: b.y + b.height / 2, w: b.width, h: b.height};
  });

  // Labels follow the existing road geometry. No additional basemap is loaded.
  const detailLayer = document.createElementNS(NS, "g");
  detailLayer.id = "navigation-labels";
  detailLayer.setAttribute("aria-hidden", "true");
  svg.querySelector("#streets").after(detailLayer);
  const labelInk = svg.querySelector("#labels text:not(.halo)")?.getAttribute("fill") || "#51493B";
  const makeDetailText = (text, kind) => {
    const el = document.createElementNS(NS, "text");
    el.textContent = text; el.classList.add(kind);
    el.setAttribute("fill", labelInk); detailLayer.appendChild(el);
    return el;
  };
  const addressText = [...byId.values()].map(a => a.address).join(" ").toLowerCase();
  const roads = [...svg.querySelectorAll('#streets path[data-name]')].map(path => {
    const name = path.dataset.name, text = name.replace(/^улица /, "ул. ").replace(/ улица$/, " ул.");
    const el = makeDetailText(text, "street-label"), width = el.getComputedTextLength();
    const pieces = (path.getAttribute("d").match(/M[^M]+/g) || []).map(d => {
      const nums = d.match(/-?\d+(?:\.\d+)?/g).map(Number);
      return nums.reduce((points, n, i) => { if (!(i % 2)) points.push({x: n, y: nums[i + 1]}); return points; }, []);
    });
    const key = name.toLowerCase().replace(/улица/g, "").trim();
    return {el, width, pieces, priority: addressText.includes(key) ? 0 : 1};
  }).sort((a, b) => a.priority - b.priority);
  const details = JSON.parse(document.getElementById("navigation-data")?.textContent || '{"houses":[]}');
  const houses = details.houses.map(h => {
    const el = makeDetailText(h.number, "house-label");
    const title = document.createElementNS(NS, "title"); title.textContent = `${h.street}, ${h.number}`; el.appendChild(title);
    return {...h, el, width: el.getComputedTextLength()};
  });
  function layoutDetails(k, occupied) {
    const zoom = FULL.w / vb.w, bounds = viewport();
    detailLayer.style.display = zoom >= 1.7 ? "" : "none";
    if (zoom < 1.7) return;
    const blocked = [...occupied];
    const place = (label, x, y, angle, fontHeight) => {
      const rad = angle * Math.PI / 180, w = label.width / k, h = fontHeight / k;
      const b = {x, y, w: Math.abs(Math.cos(rad)) * w + Math.abs(Math.sin(rad)) * h,
        h: Math.abs(Math.sin(rad)) * w + Math.abs(Math.cos(rad)) * h};
      if (!CalloutGeometry.inside(b, bounds, 6 / k) || blocked.some(o => CalloutGeometry.overlaps(b, o, 4 / k))) return false;
      label.el.setAttribute("transform", `translate(${x} ${y}) rotate(${angle}) scale(${1 / k})`);
      label.el.style.display = ""; blocked.push(b); return true;
    };
    houses.forEach(h => {
      h.el.style.display = "none";
      if (zoom >= 4) place(h, h.x, h.y, 0, 11);
    });
    roads.forEach(road => {
      road.el.style.display = "none";
      if (zoom < 2.4 && road.priority) return;
      const center = {x: bounds.x + bounds.w / 2, y: bounds.y + bounds.h / 2};
      const candidates = road.pieces.flatMap(piece => CalloutGeometry.labelCandidates(piece, (road.width + 24) / k, 32 / k))
        .map(p => ({...p, distance: Math.hypot(p.x - center.x, p.y - center.y)}));
      candidates.sort((a, b) => a.distance - b.distance)
        .some(p => place(road, p.x, p.y, p.angle, 12));
    });
  }

  const clamp = v => {
    const w = limit(v.w, FULL.w / 10, FULL.w), h = w * FULL.h / FULL.w;
    return {x: limit(v.x, 0, FULL.w - w), y: limit(v.y, 0, FULL.h - h), w, h};
  };
  const scale = (v = vb) => {
    const r = svg.getBoundingClientRect();
    return Math.min(r.width / v.w, r.height / v.h) || 1;
  };
  function toSvg(cx, cy) {
    const p = svg.createSVGPoint(); p.x = cx; p.y = cy;
    return p.matrixTransform(svg.getScreenCTM().inverse());
  }
  const markerAt = (g, f = symK) => ({
    x: +g.dataset.ax + (+g.dataset.x - +g.dataset.ax) * f,
    y: +g.dataset.ay + (+g.dataset.y - +g.dataset.ay) * f
  });
  function viewport() {
    const r = svg.getBoundingClientRect();
    const headerBottom = document.querySelector(".top").getBoundingClientRect().bottom;
    const sheetTop = mobile.matches && !sheet.hidden ? sheet.getBoundingClientRect().top : innerHeight;
    const top = Math.max(r.top, headerBottom, 0);
    const bottom = Math.min(r.bottom, innerHeight, sheetTop - (sheet.hidden ? 0 : 8)) - (vb.w < FULL.w - 1 ? 38 : 0);
    const a = toSvg(r.left, bottom > top ? top : r.top);
    const b = toSvg(r.right, bottom > top ? bottom : r.bottom);
    return {x: a.x, y: a.y, w: b.x - a.x, h: b.y - a.y};
  }
  function calloutAt(c, f = symK) {
    return {x: c.ax + (c.cx - c.ax + c.dx) * f,
      y: c.ay + (c.cy - c.ay + c.dy) * f,
      w: c.width * f * c.size, h: c.height * f * c.size};
  }
  function keepInside(p, bounds, pad) {
    return {...p, x: limit(p.x, bounds.x + p.w / 2 + pad, bounds.x + bounds.w - p.w / 2 - pad),
      y: limit(p.y, bounds.y + p.h / 2 + pad, bounds.y + bounds.h - p.h / 2 - pad)};
  }
  let layoutFrame = 0, layoutTime = 0;
  function layoutCallouts(k) {
    cancelAnimationFrame(layoutFrame);
    const bounds = viewport(), zoomed = vb.w < FULL.w - 1;
    const now = performance.now(), alpha = reduce ? 1 : 1 - Math.exp(-limit(now - layoutTime, 8, 32) / 75);
    layoutTime = now;
    const strength = limit((FULL.w / vb.w - 1) / 1.2, 0, 1);
    const obstacles = labelBoxes.map(b => ({x: b.ax + (b.x - b.ax) * symK,
      y: b.ay + (b.y - b.ay) * symK, w: b.w * symK, h: b.h * symK}));
    markers.forEach(g => {
      const m = markerAt(g);
      obstacles.push({x: m.x, y: m.y, w: 84 * symK, h: 84 * symK, marker: g.dataset.id});
    });
    pane.querySelectorAll('.map-tools').forEach(control => {
      if (control.hidden) return;
      const r = control.getBoundingClientRect(), a = toSvg(r.left - 6, r.top - 6), b = toSvg(r.right + 6, r.bottom + 6);
      obstacles.push({x: (a.x + b.x) / 2, y: (a.y + b.y) / 2, w: b.x - a.x, h: b.y - a.y});
    });
    const planned = new Map([...callouts].map(([id, c]) => {
      const p = calloutAt(c), m = markerAt(c.marker);
      const visible = m.x >= bounds.x && m.x <= bounds.x + bounds.w && m.y >= bounds.y && m.y <= bounds.y + bounds.h;
      return [id, zoomed && visible ? keepInside(p, bounds, 12 / k) : p];
    }));
    const targets = new Map();
    // Stable order and original offsets make the result independent of pan history.
    for (const [id, c] of [...callouts].sort((a, b) => +a[0] - +b[0])) {
      const natural = planned.get(id), m = markerAt(c.marker);
      const inView = m.x >= bounds.x && m.x <= bounds.x + bounds.w && m.y >= bounds.y && m.y <= bounds.y + bounds.h;
      if (!c.manual && strength > 0 && inView) {
        const blocked = [...obstacles, ...[...planned].filter(([key]) => key !== id).map(([, p]) => p)];
        const otherLines = [...callouts].filter(([key]) => key !== id).map(([key, other]) =>
          CalloutGeometry.leader(markerAt(other.marker), planned.get(key), other.radius * symK, other.square)).filter(Boolean);
        const near = CalloutGeometry.near(m, natural, c.radius * symK, blocked, bounds, 6 / k, otherLines, c.square);
        const target = {...near, x: natural.x + (near.x - natural.x) * strength,
          y: natural.y + (near.y - natural.y) * strength};
        // Do not shorten a leader by putting the drawing on a neighbouring label.
        if (!blocked.some(o => CalloutGeometry.overlaps(target, o, 3 / k))) planned.set(id, target);
      }
      targets.set(id, planned.get(id));
    }
    let settling = false;
    callouts.forEach(c => {
      const m = markerAt(c.marker), natural = calloutAt(c);
      const target = targets.get(c.g.dataset.id);
      const tx = (target.x - natural.x) / symK, ty = (target.y - natural.y) / symK;
      if (c.manual || !zoomed) { c.autoX = c.autoY = 0; }
      else {
        c.autoX += (tx - c.autoX) * alpha; c.autoY += (ty - c.autoY) * alpha;
        if (Math.hypot(tx - c.autoX, ty - c.autoY) * symK * k > .15) settling = true;
        else { c.autoX = tx; c.autoY = ty; }
      }
      const automatic = {...natural, x: natural.x + c.autoX * symK, y: natural.y + c.autoY * symK};
      // At close zoom a nearby drawing stays in view with its marker. Do not rewrite
      // the saved offset while panning: returning to an area restores its placement.
      const inView = m.x >= bounds.x && m.x <= bounds.x + bounds.w
        && m.y >= bounds.y && m.y <= bounds.y + bounds.h;
      const p = zoomed && inView ? keepInside(automatic, bounds, 12 / k) : automatic;
      c.display = p;
      c.g.setAttribute("transform", `translate(${p.x} ${p.y}) scale(${symK * c.size}) translate(${-c.cx} ${-c.cy})`);
    });
    const routed = [];
    callouts.forEach((c, id) => {
      const m = markerAt(c.marker), p = c.display;
      c.leader.removeAttribute("transform");
      const line = CalloutGeometry.leader(m, p, c.radius * symK, c.square);
      const visible = line && line.length > 4 / k;
      c.leader.style.display = visible ? "" : "none";
      if (visible) {
        const boxes = [...obstacles.filter(o => o.marker !== id), ...[...callouts.values()].map(other => other.display)];
        const points = CalloutGeometry.route(line, boxes, routed, 7 / k, bounds);
        // Clip the first leg to the marker in its actual direction after a detour.
        const attachment = CalloutGeometry.leader(m, {...points[1], w: 0, h: 0}, c.radius * symK, c.square);
        if (attachment) points[0] = attachment.start;
        c.leader.setAttribute("d", points.map((p, i) => `${i ? "L" : "M"}${p.x} ${p.y}`).join(""));
        routed.push(...CalloutGeometry.segments(points));
      }
      // The dotted line keeps the same weight as the original at every zoom;
      // resizing the drawing does not also thicken its leader.
      c.leader.setAttribute("stroke-width", 4 * symK);
      c.leader.setAttribute("stroke-dasharray", `${.1 * symK} ${9 * symK}`);
    });
    layoutDetails(k, [...obstacles, ...[...callouts.values()].map(c => c.display)]);
    if (settling) layoutFrame = requestAnimationFrame(() => layoutCallouts(scale()));
  }
  function updateToolbar() {
    const c = callouts.get(editing);
    toolbar.hidden = !c;
    if (!c) return;
    toolbar.querySelector("span").textContent = `Рисунок №${editing}`;
    toolbar.querySelector('[data-size="smaller"]').disabled = c.size <= .6;
    toolbar.querySelector('[data-size="larger"]').disabled = c.size >= 1.8;
    positionToolbar();
  }
  function positionToolbar() {
    if (toolbar.hidden) return;
    const r = pane.getBoundingClientRect();
    const top = document.querySelector(".top").getBoundingClientRect().bottom;
    toolbar.style.top = `${limit(top - r.top + 12, 12, Math.max(12, r.height - toolbar.offsetHeight - 12))}px`;
  }
  function editCallout(id) {
    editing = id;
    highlightCallouts();
    updateToolbar();
  }
  function highlightCallouts() {
    callouts.forEach((c, id) => {
      const on = id === active || id === editing;
      c.g.classList.toggle("is-active", on); c.leader.classList.toggle("is-active", on);
      c.g.setAttribute("aria-pressed", String(on));
      if (on) {
        if (c.leader.parentNode.lastElementChild !== c.leader) c.leader.parentNode.appendChild(c.leader);
        // Re-inserting the focused SVG group makes browsers drop keyboard focus.
        if (document.activeElement !== c.g && c.g.parentNode.lastElementChild !== c.g) c.g.parentNode.appendChild(c.g);
      }
    });
  }
  function positionMapTools() {
    const isOpen = mobile.matches && !sheet.hidden, r = pane.getBoundingClientRect();
    // Give the SVG the usable height on short phones. This also lets places
    // near the south edge remain visible when the description is expanded.
    pane.style.setProperty("--map-canvas-height", isOpen ? `${Math.max(120, Math.min(r.height, sheet.getBoundingClientRect().top - r.top - 8))}px` : "100%");
    const bottom = isOpen ? Math.max(12, r.bottom - sheet.getBoundingClientRect().top + 12) : 12;
    pane.querySelector('.map-tools:not(.callout-tools)').style.bottom = `${bottom}px`;
    dynScale.style.bottom = `${bottom}px`;
  }
  function apply(v) {
    vb = v;
    svg.setAttribute("viewBox", `${v.x} ${v.y} ${v.w} ${v.h}`);
    const zoomed = v.w < FULL.w - 1;
    svg.classList.toggle("is-zoomed", zoomed);
    pane.classList.toggle("is-zoomed", zoomed);
    const k = scale();
    symK = Math.min(1, SYM_PX / k);
    syms.forEach(s => {
      if (symK === 1) s.g.removeAttribute("transform");
      else s.g.setAttribute("transform", `translate(${s.ax} ${s.ay}) scale(${symK}) translate(${-s.ax} ${-s.ay})`);
    });
    hits.forEach(c => c.setAttribute("r", Math.max(44, 22 / (k * symK))));
    positionToolbar();
    positionMapTools();
    layoutCallouts(k);
    const pxPerM = PX_PER_M * k;
    let d = 20;
    for (const n of [20, 50, 100, 200, 300, 500, 1000, 2000]) if (n * pxPerM <= 130) d = n;
    dynScale.querySelector("i").style.width = `${(d * pxPerM).toFixed(0)}px`;
    dynScale.querySelector("span").textContent = d >= 1000 ? `${d / 1000} км` : `${d} м`;
  }
  const ease = t => t < .5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
  function animateTo(target, ms = 450) {
    const t = clamp(target);
    cancelAnimationFrame(anim);
    if (reduce) return apply(t);
    const s = {...vb}, t0 = performance.now();
    const step = now => {
      const t1 = Math.min(1, (now - t0) / ms), e = ease(t1);
      apply({x: s.x + (t.x - s.x) * e, y: s.y + (t.y - s.y) * e,
        w: s.w + (t.w - s.w) * e, h: s.h + (t.h - s.h) * e});
      if (t1 < 1) anim = requestAnimationFrame(step);
    };
    anim = requestAnimationFrame(step);
  }
  function zoomTarget(px, py, factor, base = vb) {
    const w = limit(base.w / factor, FULL.w / 10, FULL.w), ratio = w / base.w;
    return clamp({x: px - (px - base.x) * ratio, y: py - (py - base.y) * ratio, w});
  }
  function focusOn(id) {
    const g = markers.get(id), c = callouts.get(id);
    // Preserve a closer zoom; fit the true location, marker AND moved thumbnail.
    const rect = svg.getBoundingClientRect();
    const readableWidth = Math.min(rect.width, rect.height * FULL.w / FULL.h) / SYM_PX;
    let w = Math.max(FULL.w / 10, Math.min(vb.w, FULL.w / 3, readableWidth)), target;
    for (let i = 0; i < 8; i++) {
      const h = w * FULL.h / FULL.w, k = scale({w, h}), f = Math.min(1, SYM_PX / k);
      const m = markerAt(g, f), p = c && calloutAt(c, f);
      const x0 = Math.min(+g.dataset.ax, m.x - 48 * f, p ? p.x - p.w / 2 : m.x);
      const x1 = Math.max(+g.dataset.ax, m.x + 48 * f, p ? p.x + p.w / 2 : m.x);
      const y0 = Math.min(+g.dataset.ay, m.y - 48 * f, p ? p.y - p.h / 2 : m.y);
      const y1 = Math.max(+g.dataset.ay, m.y + 48 * f, p ? p.y + p.h / 2 : m.y);
      // On a tall mobile sheet, center the place in the part visible below the header.
      const r = svg.getBoundingClientRect(), header = document.querySelector(".top").getBoundingClientRect().bottom;
      const bottom = mobile.matches && !sheet.hidden ? Math.min(innerHeight, sheet.getBoundingClientRect().top - 8) : innerHeight;
      const visibleTop = Math.max(r.top, header), visibleBottom = Math.min(r.bottom, bottom) - 38;
      const availableHeight = Math.max(80, visibleBottom - visibleTop);
      const needed = w * Math.max(((x1 - x0) * k + 64) / r.width, ((y1 - y0) * k + 48) / availableHeight);
      const offsetY = (r.top + r.height / 2 - (visibleTop + visibleBottom) / 2) / k;
      target = {x: (x0 + x1 - w) / 2, y: (y0 + y1 - h) / 2 + offsetY, w};
      if (needed <= w + 1 || w >= FULL.w) break;
      w = Math.min(FULL.w, needed);
    }
    animateTo(target);
  }
  function select(id, from) {
    const g = markers.get(id), c = cards.get(id);
    if (!g || !c) return;
    if (active) {
      markers.get(active)?.classList.remove("is-active");
      cards.get(active)?.classList.remove("is-active");
    }
    active = id;
    g.classList.add("is-active"); c.classList.add("is-active");
    highlightCallouts();
    if (document.activeElement !== g && g.parentNode.lastElementChild !== g) g.parentNode.appendChild(g);
    const a = byId.get(id);
    announce.textContent = `Выбрано: ${a.id}. ${a.name}, ${a.category}`;
    if (mobile.matches) showSheet(id);
    if (from === "map") {
      editCallout(null);
      if (mobile.matches) focusOn(id);
      else {
        c.scrollIntoView({behavior: reduce ? "auto" : "smooth", block: "center"});
        c.classList.remove("flash"); void c.offsetWidth; c.classList.add("flash");
      }
    } else if (from === "list") {
      editCallout(null);
      const r = pane.getBoundingClientRect();
      const header = document.querySelector(".top").getBoundingClientRect().bottom;
      if (r.top < header - 1 || r.top > header + 40)
        pane.scrollIntoView({behavior: mobile.matches || reduce ? "auto" : "smooth", block: "start"});
      focusOn(id);
    } else { editCallout(id); layoutCallouts(scale()); }
    history.replaceState(null, "", "#p" + id);
  }
  function nearest(p) {
    let best = null, bd = Infinity;
    markers.forEach((g, id) => {
      const m = markerAt(g), d = Math.hypot(m.x - p.x, m.y - p.y);
      if (d < bd) { bd = d; best = id; }
    });
    return bd <= Math.max(48 * symK, 26 / scale()) ? best : null;
  }
  function moveCallout(c, x, y) {
    c.manual = true; c.autoX = c.autoY = 0;
    const p = keepInside({...calloutAt(c), x, y}, viewport(), 12 / scale());
    c.dx = (p.x - c.ax) / symK - (c.cx - c.ax);
    c.dy = (p.y - c.ay) / symK - (c.cy - c.ay);
    layoutCallouts(scale());
  }
  function resizeCallout(c, size) {
    cancelAnimationFrame(anim);
    c.size = limit(size, .6, 1.8);
    layoutCallouts(scale());
    updateToolbar();
  }
  function resetCallout(c) {
    c.dx = c.dy = 0; c.size = 1; c.manual = false;
    layoutCallouts(scale()); updateToolbar();
  }
  toolbar.addEventListener("click", e => {
    const c = callouts.get(editing), action = e.target.closest("button")?.dataset.size;
    if (!c || !action) return;
    if (action === "reset") resetCallout(c);
    else resizeCallout(c, c.size * (action === "larger" ? 1.2 : 1 / 1.2));
  });

  // Each gesture has a fresh baseline. Rebase when a second finger arrives or
  // leaves, and release captures even outside the SVG or after pointercancel.
  const pointers = new Map();
  let gesture = null, suppressClick = false;
  const midpoint = (a, b) => ({x: (a.x + b.x) / 2, y: (a.y + b.y) / 2});
  function beginGesture() {
    const ps = [...pointers.values()];
    if (!ps.length) { gesture = null; return; }
    const p = ps[0];
    if (ps.length >= 2) {
      const mid = midpoint(p, ps[1]), c = p.id && p.id === ps[1].id && callouts.get(p.id);
      gesture = {kind: c ? "resize" : "pinch", c, vb: {...vb}, mid, k: scale(),
        anchor: toSvg(mid.x, mid.y), distance: Math.max(1, Math.hypot(p.x - ps[1].x, p.y - ps[1].y)),
        size: c?.size, center: c && {...c.display}};
      suppressClick = true;
    } else {
      const c = p.id && callouts.get(p.id);
      gesture = {kind: c ? "callout" : "pan", c, x: p.x, y: p.y, vb: {...vb},
        k: scale(), center: c && {...c.display}, moved: false};
    }
  }
  svg.addEventListener("pointerdown", e => {
    if (e.button !== 0 || pointers.size >= 2) return;
    cancelAnimationFrame(anim);
    if (!pointers.size) suppressClick = false;
    const id = e.target.closest(".illu")?.dataset.id || null;
    pointers.set(e.pointerId, {x: e.clientX, y: e.clientY, id, type: e.pointerType});
    if (id) { editCallout(id); callouts.get(id).g.focus({preventScroll: true}); }
    else editCallout(null);
    svg.setPointerCapture(e.pointerId);
    beginGesture();
  });
  svg.addEventListener("pointermove", e => {
    const pointer = pointers.get(e.pointerId);
    if (!pointer || !gesture) return;
    Object.assign(pointer, {x: e.clientX, y: e.clientY});
    if (pointers.size === 2) {
      const [a, b] = [...pointers.values()], mid = midpoint(a, b);
      const factor = Math.hypot(a.x - b.x, a.y - b.y) / gesture.distance;
      if (gesture.kind === "resize") {
        resizeCallout(gesture.c, gesture.size * factor);
        moveCallout(gesture.c, gesture.center.x + (mid.x - gesture.mid.x) / gesture.k,
          gesture.center.y + (mid.y - gesture.mid.y) / gesture.k);
      } else {
        const v = zoomTarget(gesture.anchor.x, gesture.anchor.y, factor, gesture.vb);
        // Translation of the midpoint is part of a pinch, even at zoom limits.
        const k = scale(v);
        v.x -= (mid.x - gesture.mid.x) / k; v.y -= (mid.y - gesture.mid.y) / k;
        apply(clamp(v));
      }
      return;
    }
    if (gesture.kind === "pan" && vb.w >= FULL.w - 1 && pointer.type === "touch") return;
    const dx = e.clientX - gesture.x, dy = e.clientY - gesture.y;
    if (!gesture.moved && Math.hypot(dx, dy) < 6) return;
    gesture.moved = suppressClick = true;
    svg.classList.add("is-dragging");
    if (gesture.c) {
      gesture.c.g.classList.add("is-dragging");
      moveCallout(gesture.c, gesture.center.x + dx / gesture.k, gesture.center.y + dy / gesture.k);
    } else apply(clamp({...gesture.vb, x: gesture.vb.x - dx / gesture.k, y: gesture.vb.y - dy / gesture.k}));
  });
  function finishPointer(e) {
    if (!pointers.has(e.pointerId)) return;
    pointers.delete(e.pointerId);
    if (e.type !== "pointerup") suppressClick = true;
    if (svg.hasPointerCapture(e.pointerId)) svg.releasePointerCapture(e.pointerId);
    svg.classList.remove("is-dragging");
    callouts.forEach(c => c.g.classList.remove("is-dragging"));
    beginGesture();
  }
  ["pointerup", "pointercancel", "lostpointercapture"].forEach(name => svg.addEventListener(name, finishPointer));
  addEventListener("blur", () => {
    for (const id of [...pointers.keys()]) finishPointer({pointerId: id, type: "pointercancel"});
  });
  svg.addEventListener("click", e => {
    if (suppressClick) { suppressClick = false; return; }
    // Pointer capture retargets click to the SVG. Resolve the actual release point.
    const target = document.elementFromPoint(e.clientX, e.clientY);
    const ill = target?.closest(".illu");
    if (ill) return select(ill.dataset.id, "illustration");
    const id = nearest(toSvg(e.clientX, e.clientY));
    if (id) select(id, "map");
  });
  svg.addEventListener("dblclick", e => {
    const ill = document.elementFromPoint(e.clientX, e.clientY)?.closest(".illu");
    if (ill) { resetCallout(callouts.get(ill.dataset.id)); return; }
    const p = toSvg(e.clientX, e.clientY);
    animateTo(zoomTarget(p.x, p.y, 2), 300);
  });
  svg.addEventListener("wheel", e => {
    e.preventDefault();
    if (pointers.size) return;
    const unit = e.deltaMode === 1 ? 16 : e.deltaMode === 2 ? svg.clientHeight : 1;
    const delta = limit(e.deltaY * unit, -300, 300);
    const ill = e.target.closest(".illu");
    if (ill && e.shiftKey) {
      editCallout(ill.dataset.id);
      const c = callouts.get(editing);
      resizeCallout(c, c.size * Math.exp(-delta * .003));
      return;
    }
    cancelAnimationFrame(anim);
    const p = toSvg(e.clientX, e.clientY);
    apply(zoomTarget(p.x, p.y, Math.exp(-delta * (e.ctrlKey ? .01 : .0025))));
  }, {passive: false});

  const hover = (id, on) => {
    markers.get(id)?.classList.toggle("is-hover", on);
    cards.get(id)?.classList.toggle("is-hover", on);
    callouts.get(id)?.g.classList.toggle("is-hover", on);
    callouts.get(id)?.leader.classList.toggle("is-hover", on);
  };
  callouts.forEach((c, id) => {
    c.g.addEventListener("pointerenter", () => hover(id, true));
    c.g.addEventListener("pointerleave", () => hover(id, false));
    c.g.addEventListener("focus", () => editCallout(id));
    c.g.addEventListener("keydown", e => {
      if (["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown"].includes(e.key)) {
        e.preventDefault();
        const step = (e.shiftKey ? 30 : 10) / scale();
        moveCallout(c, c.display.x + (e.key === "ArrowLeft" ? -step : e.key === "ArrowRight" ? step : 0),
          c.display.y + (e.key === "ArrowUp" ? -step : e.key === "ArrowDown" ? step : 0));
      } else if (["+", "=", "-", "_"].includes(e.key)) {
        e.preventDefault(); resizeCallout(c, c.size * (["+", "="].includes(e.key) ? 1.2 : 1 / 1.2));
      } else if (e.key === "0" || e.key === "Home") {
        e.preventDefault(); resetCallout(c);
      } else if (e.key === "Enter" || e.key === " ") {
        e.preventDefault(); select(id, "illustration");
      }
    });
  });
  markers.forEach((g, id) => {
    g.addEventListener("keydown", e => {
      if (e.key === "Enter" || e.key === " ") { e.preventDefault(); select(id, "map"); }
    });
    g.addEventListener("pointerenter", () => hover(id, true));
    g.addEventListener("pointerleave", () => hover(id, false));
  });
  cards.forEach((c, id) => {
    c.querySelector(".card-hit").addEventListener("click", () => select(id, "list"));
    c.addEventListener("pointerenter", () => hover(id, true));
    c.addEventListener("pointerleave", () => hover(id, false));
  });
  document.querySelectorAll("[data-zoom]").forEach(b => b.addEventListener("click", () => {
    const bounds = viewport(), cx = bounds.x + bounds.w / 2, cy = bounds.y + bounds.h / 2;
    if (b.dataset.zoom === "reset") {
      callouts.forEach(c => { c.dx = c.dy = 0; c.size = 1; c.manual = false; });
      closeSheet();
      editCallout(null); animateTo(FULL);
    } else animateTo(zoomTarget(cx, cy, b.dataset.zoom === "in" ? 1.6 : 1 / 1.6), 300);
  }));
  document.addEventListener("keydown", e => {
    if (e.key !== "Escape") return;
    if (!sheet.hidden && mobile.matches) closeSheet(true);
    else if (editing) editCallout(null);
    else animateTo(FULL);
  });
  const resetButton = document.querySelector('[data-zoom="reset"]');
  resetButton.title = "Показать всю карту и вернуть миниатюры на исходные места";
  let previousWidth = svg.clientWidth, previousHeight = svg.clientHeight;
  const observer = new ResizeObserver(() => {
    if (svg.clientWidth === previousWidth && svg.clientHeight === previousHeight) return;
    previousWidth = svg.clientWidth; previousHeight = svg.clientHeight;
    apply(clamp(vb));
    if (pointers.size) beginGesture();
  });
  observer.observe(svg);
  let scrollFrame = 0;
  addEventListener("scroll", () => {
    cancelAnimationFrame(scrollFrame);
    scrollFrame = requestAnimationFrame(() => {
      if (!sheet.hidden && pane.getBoundingClientRect().bottom < document.querySelector('.top').getBoundingClientRect().bottom + 80) sheet.hidden = true;
      layoutCallouts(scale()); positionToolbar(); positionMapTools();
    });
  }, {passive: true});
  apply(vb);
  const hash = location.hash.match(/^#p(\d+)$/);
  if (hash && markers.has(hash[1])) {
    history.scrollRestoration = "manual";
    const openPlace = () => select(hash[1], "list");
    if (document.readyState === "complete") openPlace();
    else addEventListener("load", openPlace, {once: true});
  }
})();
