const assert = require('node:assert/strict');
const test = require('node:test');
const {leader, near, overlaps, inside, intersects, throughBox, route, segments, labelCandidates} = require('../map_navigation.js');

const bounds = {x: 0, y: 0, w: 1000, h: 1000};
const marker = {x: 500, y: 500};
const original = {x: 760, y: 300, w: 100, h: 90};

test('a free thumbnail moves substantially closer to its marker', () => {
  const p = near(marker, original, 20, [], bounds, 6);
  assert(Math.hypot(p.x - marker.x, p.y - marker.y) < 100);
  assert(inside(p, bounds, 6));
});

test('near placement avoids labels, markers and occupied thumbnails', () => {
  const blocked = [{x: 500, y: 410, w: 160, h: 120}, {x: 590, y: 500, w: 130, h: 160}];
  const p = near(marker, original, 20, blocked, bounds, 6);
  assert.notDeepEqual(p, original);
  blocked.forEach(b => assert(!overlaps(p, b, 6)));
});

test('keeps the existing placement if there is no free space closer', () => {
  const p = near(marker, original, 20, [{x: 500, y: 500, w: 500, h: 500}], bounds, 6);
  assert.deepEqual(p, original);
});

test('more space after zoom allows a previously blocked drawing to approach', () => {
  const compact = [{x: 500, y: 500, w: 500, h: 500}];
  const expanded = [{x: 800, y: 800, w: 100, h: 100}];
  assert.deepEqual(near(marker, original, 20, compact, bounds, 6), original);
  assert.notDeepEqual(near(marker, original, 20, expanded, bounds, 6), original);
});

test('placement at the viewport edge stays visible', () => {
  const m = {x: 20, y: 20}, p = near(m, {...original, x: 300, y: 300}, 20, [], bounds, 6);
  assert(inside(p, bounds, 6));
  assert(p.x > m.x && p.y > m.y);
});

test('circular leader starts at the marker edge and ends at the thumbnail edge', () => {
  const p = {x: 630, y: 350, w: 100, h: 80};
  const line = leader(marker, p, 20, false);
  assert(Math.abs(Math.hypot(line.start.x - 500, line.start.y - 500) - 20) < 1e-8);
  assert.equal(line.end.x, 580);
  assert.equal(line.end.y, 390);
});

test('square marker and resized thumbnail have accurate leader endpoints', () => {
  const a = leader(marker, {x: 700, y: 400, w: 100, h: 100}, 20, true);
  const b = leader(marker, {x: 700, y: 400, w: 180, h: 180}, 20, true);
  assert.equal(a.start.x, 520);
  assert.equal(b.start.x, 520);
  assert.equal(a.end.x, 650);
  assert.equal(b.end.x, 610);
  assert(b.length < a.length);
});

test('a thumbnail on top of its marker has no reversed or non-finite leader', () => {
  assert.equal(leader(marker, {x: 500, y: 500, w: 80, h: 80}, 20, true), null);
  assert.equal(leader(marker, {x: 535, y: 500, w: 40, h: 40}, 20, false), null);
});

test('scaling and translating the scene preserves attachment geometry', () => {
  const p = {x: 700, y: 400, w: 100, h: 100};
  const a = leader(marker, p, 20, true);
  const f = .35, dx = 150, dy = -40;
  const map = q => ({x: q.x * f + dx, y: q.y * f + dy});
  const b = leader(map(marker), {...map(p), w: p.w * f, h: p.h * f}, 20 * f, true);
  for (const key of ['start', 'end']) {
    assert(Math.abs(b[key].x - map(a[key]).x) < 1e-8);
    assert(Math.abs(b[key].y - map(a[key]).y) < 1e-8);
  }
});

test('crossing, parallel and overlapping leaders are distinguished', () => {
  const a = {start:{x:0,y:0},end:{x:100,y:100}};
  assert(intersects(a, {start:{x:0,y:100},end:{x:100,y:0}}));
  assert(!intersects(a, {start:{x:0,y:10},end:{x:100,y:110}}));
  assert(!intersects(a, {start:a.end,end:{x:120,y:90}}));
  assert(intersects(a, {start:{x:50,y:50},end:{x:150,y:150}}));
});

test('a detour clears a drawing without changing its attachment endpoint', () => {
  const line = {start:{x:100,y:300},end:{x:600,y:300}};
  const obstacle = {x:350,y:300,w:130,h:160};
  const points = route(line, [obstacle], [], 10, bounds);
  assert(points.length > 2);
  assert.deepEqual(points[0],line.start); assert.deepEqual(points.at(-1),line.end);
  assert(segments(points).every(s => !throughBox(s, obstacle)));
});

test('a crossing is routed around an existing leader', () => {
  const line = {start:{x:100,y:300},end:{x:600,y:300}};
  const other = {start:{x:350,y:240},end:{x:350,y:360}};
  const points = route(line, [], [other], 10, bounds);
  assert(points.length > 2);
  assert(segments(points).every(s => !intersects(s, other)));
});

test('free leaders remain straight and tangent box edges are not obstructions', () => {
  const line = {start:{x:100,y:100},end:{x:300,y:100}};
  assert.deepEqual(route(line, [], [], 10, bounds),[line.start,line.end]);
  assert(!throughBox(line,{x:200,y:150,w:100,h:100}));
});

test('near placement chooses a free side instead of crossing another leader', () => {
  const old = {x:500,y:180,w:100,h:90};
  const other = {start:{x:350,y:470},end:{x:650,y:470}};
  const p = near(marker, old, 20, [], bounds, 6, [other]);
  assert(!intersects(leader(marker,p,20,false),other));
  assert(Math.hypot(p.x-500,p.y-500)<Math.hypot(old.x-500,old.y-500));
});

test('street labels span short collinear pieces but avoid a sharp bend', () => {
  const line = [{x:0,y:0},{x:30,y:0},{x:60,y:0},{x:120,y:0}];
  assert(labelCandidates(line,100,20).length > 0);
  const bent = [{x:0,y:0},{x:60,y:0},{x:60,y:60}];
  assert.equal(labelCandidates(bent,100,20).length,0);
  labelCandidates([...line].reverse(),100,20).forEach(p => assert(Math.abs(p.angle)<=90));
});
