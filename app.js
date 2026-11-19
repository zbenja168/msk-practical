'use strict';
const $ = (id) => document.getElementById(id);
const LS = { get(k, d) { try { const v = localStorage.getItem(k); return v == null ? d : JSON.parse(v); } catch (e) { return d; } },
             set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} } };

// ---------- typed-answer matching (shared with the 3D Anatomy Trainer) ----------
const norm = (s) => String(s || '').toLowerCase().normalize('NFD').replace(/[̀-ͯ]/g, '')
  .replace(/&/g, ' and ').replace(/[^a-z0-9]+/g, ' ').trim();
const GENERIC = new Set(['the', 'of', 'm', 'muscle', 'muscles', 'nerve', 'n', 'artery', 'a', 'vein', 'v', 'bone', 'and', 'left', 'right', 'l', 'r', 'tendon']);
const strip = (s) => norm(s).split(' ').filter((w) => !GENERIC.has(w)).join(' ');
function lev(a, b) {
  const m = a.length, n = b.length; let prev = Array.from({ length: n + 1 }, (_, j) => j);
  for (let i = 1; i <= m; i++) { const cur = [i]; for (let j = 1; j <= n; j++) cur[j] = Math.min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1)); prev = cur; }
  return prev[n];
}
const tol = (s) => s.length <= 4 ? 0 : s.length <= 8 ? 1 : s.length <= 15 ? 2 : 3;
function formsOf(names) {
  const forms = [];
  names.forEach((s) => {
    forms.push(s, s.replace(/\s*\(.*?\)\s*/g, ' '));
    (s.match(/\(([^)]*)\)/g) || []).forEach((m) => m.slice(1, -1).split(/[,/;]| or /).forEach((x) => forms.push(x)));
    s.split(/\s*\/\s*/).forEach((x) => forms.push(x));
  });
  return [...new Set(forms.map(strip).filter((x) => x.length > 1))];
}
const CONTRAST = [
  ['major', 'minor'], ['superior', 'inferior', 'middle'], ['anterior', 'posterior'], ['medial', 'lateral', 'intermediate'],
  ['internal', 'external'], ['greater', 'lesser'], ['longus', 'brevis', 'magnus'], ['longissimus', 'iliocostalis', 'spinalis'],
  ['maximus', 'medius', 'minimus'], ['superficial', 'deep'], ['superficialis', 'profundus'], ['proximal', 'distal'],
  ['upper', 'lower'], ['ascending', 'descending'], ['abductor', 'adductor'], ['flexor', 'extensor'], ['supinator', 'pronator'],
  ['dorsal', 'palmar', 'plantar', 'ventral'], ['radial', 'ulnar'], ['tibial', 'fibular', 'peroneal'], ['hallucis', 'pollicis'],
  ['long', 'short'], ['quadratus', 'teres'], ['supraspinatus', 'infraspinatus'], ['supraspinous', 'infraspinous'],
  ['supraclavicular', 'infraclavicular'], ['suprascapular', 'subscapular'], ['carpi', 'digitorum'], ['interossei', 'lumbricals'],
  ['first', 'second', 'third', 'fourth', 'fifth'], ['1', '2', '3', '4', '5', '6', '7', '8', '9', '10', '11', '12'],
  ['cervical', 'thoracic', 'lumbar', 'sacral', 'coccygeal'], ['artery', 'vein'], ['oblique', 'transverse'],
  ['ileum', 'ilium'], ['ileal', 'iliac'], ['perineal', 'peroneal'], ['capitis', 'cervicis', 'thoracis'],
  ['femoris', 'brachii'], ['semitendinosus', 'semimembranosus'], ['cephalic', 'basilic'], ['gemellus', 'gemelli'],
];
const CGROUP = new Map(); CONTRAST.forEach((g, i) => g.forEach((w) => CGROUP.set(w, (CGROUP.get(w) || []).concat(i))));
function contrastClash(typed, form) {
  const tw = norm(typed).split(' '), fw = new Set(norm(form).split(' '));
  return tw.some((w) => !fw.has(w) && (CGROUP.get(w) || []).some((gi) => CONTRAST[gi].some((o) => o !== w && fw.has(o))));
}
// names: accepted answers (each may carry "(alt, alt)" / "a / b" alternatives)
function typedOk(typed, names) {
  const t = strip(typed); if (!t) return false;
  return names.some((n) => formsOf([n]).some((f) => (lev(t, f) <= tol(f) || (f.length > 10 && t.length >= 6 && f.startsWith(t) && t.length >= f.length * 0.7)))
    && !contrastClash(typed, n));
}

// ---------- state ----------
let BANK = null, HY = [], BYID = new Map(), CTX = {}, POLY = {}, IMGST = new Map();
// The full bank needs an Active Transport sign-in; High Yield is open to everyone.
let FULL = 'checking'; // 'ok' | 'locked' | 'error' | 'checking'
const cfg = Object.assign({ mode: 'hy', regions: [], type: 'mixed', rel: true, unv: true, count: 0, timer: 0 }, LS.get('mskp_cfg', {}));
// v3: High Yield (all 100) became the default; move earlier saved settings over once
if (!(cfg.v >= 3)) { cfg.mode = 'hy'; cfg.count = 0; cfg.v = 3; }
let queue = [], qi = 0, score = 0, log = [], cur = null, answered = false, pin = null, tleft = 0, tid = null, showOrig = false;

const TYPES = [['mixed', 'Mixed'], ['name', 'Name it (arrow)'], ['pin', 'Pin it (drop a marker)']];
const COUNTS = [10, 25, 50, 0];
const TIMERS = [0, 60, 90];
const KIND_WORD = { muscle: 'muscle', nerve: 'nerve', artery: 'artery', vein: 'vein', bone: 'bony structure', ligament: 'structure', joint: 'structure', space: 'space', other: 'structure' };

function chip(label, on, fn, sub) {
  const b = document.createElement('button'); b.className = 'chip' + (on ? ' on' : ''); b.type = 'button';
  b.innerHTML = label + (sub != null ? ` <small>${sub}</small>` : ''); b.onclick = fn; return b;
}
function stationsFor(c) {
  const R = new Set(c.regions.length ? c.regions : BANK.regions.map((r) => r.id));
  const inR = (s) => BANK.structs[s.s].regions.some((r) => R.has(r));
  if (c.mode === 'hy') return HY.map((h) => { const s = BYID.get(h.id); return s && Object.assign({}, s, { qtype: h.type, qrel: h.rel }); }).filter((s) => s && inR(s));
  return BANK.stations.filter((s) => (c.unv || s.sure) && inR(s));
}
function renderSetup() {
  const md = $('modes'); md.innerHTML = '';
  const hy = cfg.mode === 'hy';
  if (HY.length) md.append(chip('High Yield', hy, () => { cfg.mode = 'hy'; saveCfg(); renderSetup(); }, HY.length));
  const fb = chip((FULL === 'ok' ? '' : '&#128274; ') + 'Full bank', !hy, () => { if (FULL !== 'ok') return; cfg.mode = 'all'; saveCfg(); renderSetup(); }, BANK.stations.length);
  fb.disabled = FULL !== 'ok'; md.append(fb);
  const ln = $('fullNote');
  ln.hidden = FULL === 'ok';
  ln.innerHTML = FULL === 'locked' ? 'The full bank of ' + BANK.stations.length + ' stations unlocks when you open MSK Practical from your <a href="https://activetransport.app" target="_blank" rel="noopener">Active Transport</a> home page while signed in (any free account).'
    : FULL === 'error' ? "Couldn't check your Active Transport sign-in just now. Reload to try again." : 'Checking your Active Transport sign-in&hellip;';
  $('hyNote').hidden = !hy; $('grpTypes').hidden = hy; $('grpOpts').hidden = hy;
  const rg = $('regions'); rg.innerHTML = '';
  const all = cfg.regions.length === 0;
  rg.append(chip('All', all, () => { cfg.regions = []; saveCfg(); renderSetup(); }, stationsFor(Object.assign({}, cfg, { regions: [] })).length));
  BANK.regions.forEach((r) => {
    const n = stationsFor(Object.assign({}, cfg, { regions: [r.id] })).length;
    rg.append(chip(r.title, cfg.regions.includes(r.id), () => {
      const i = cfg.regions.indexOf(r.id); if (i >= 0) cfg.regions.splice(i, 1); else cfg.regions.push(r.id);
      saveCfg(); renderSetup();
    }, n));
  });
  const ty = $('types'); ty.innerHTML = '';
  TYPES.forEach(([k, l]) => ty.append(chip(l, cfg.type === k, () => { cfg.type = k; saveCfg(); renderSetup(); })));
  const ct = $('counts'); ct.innerHTML = '';
  COUNTS.forEach((n) => ct.append(chip(n ? String(n) : 'All', cfg.count === n, () => { cfg.count = n; saveCfg(); renderSetup(); })));
  const tm = $('timers'); tm.innerHTML = '';
  TIMERS.forEach((n) => tm.append(chip(n ? n + ' s' : 'Off', cfg.timer === n, () => { cfg.timer = n; saveCfg(); renderSetup(); })));
  $('optRel').checked = cfg.rel; $('optUnv').checked = cfg.unv;
  const st = stationsFor(cfg), ns = new Set(st.map((s) => s.s)).size;
  $('pool').textContent = `${hy ? 'High Yield: ' : ''}${st.length} stations covering ${ns} structures on ${new Set(st.map((s) => s.img)).size} photos`;
  $('btnStart').disabled = !st.length;
}
function saveCfg() { LS.set('mskp_cfg', cfg); }

// ---------- building a set ----------
function shuffle(a) { for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; }
function pickType(st) {
  const s = BANK.structs[st.s]; const canRel = cfg.rel && s.rel && s.rel.length;
  if (cfg.type === 'name') return canRel && Math.random() < 0.3 ? 'rel' : 'name';
  if (cfg.type === 'pin') return 'pin';
  const r = Math.random();
  if (canRel && r < 0.25) return 'rel';
  return r < 0.62 ? 'name' : 'pin';
}
function buildQueue(onlyStations) {
  let st = onlyStations || stationsFor(cfg);
  const byS = new Map(); st.forEach((x) => { if (!byS.has(x.s)) byS.set(x.s, []); byS.get(x.s).push(x); });
  const keys = shuffle([...byS.keys()]); byS.forEach((v) => shuffle(v));
  const want = onlyStations ? st.length : (cfg.count || st.length);
  const out = []; let round = 0;
  while (out.length < want) {
    let added = 0;
    for (const k of keys) { const v = byS.get(k); if (round < v.length) { out.push(v[round]); added++; if (out.length >= want) break; } }
    if (!added) break; round++;
  }
  // avoid the same photo back to back
  for (let i = 1; i < out.length; i++) if (out[i].img === out[i - 1].img) { const j = out.findIndex((x, k) => k > i && x.img !== out[i - 1].img); if (j > 0) [out[i], out[j]] = [out[j], out[i]]; }
  return out.map((x) => ({ st: x, type: x.qtype || pickType(x), relIdx: x.qrel == null ? null : x.qrel, rel: null }));
}

// ---------- drawing ----------
const SVGNS = 'http://www.w3.org/2000/svg';
function el(tag, attrs) { const e = document.createElementNS(SVGNS, tag); for (const k in attrs) e.setAttribute(k, attrs[k]); return e; }
function arrowFor(st, im) {
  const [tx, ty] = st.tips[0]; let dx, dy;
  if (st.tail) { dx = st.tail[0] - tx; dy = st.tail[1] - ty; }
  else { dx = tx < im.w / 2 ? -1 : 1; dy = -0.35; }
  const L = Math.hypot(dx, dy) || 1; dx /= L; dy /= L;
  const want = Math.max(70, im.w * 0.13);
  // longest tail that stays inside the picture along direction (ux, uy)
  const fit = (ux, uy) => { let len = want; for (let k = 0; k < 20; k++) { const x = tx + ux * len, y = ty + uy * len; if (x > 8 && y > 8 && x < im.w - 8 && y < im.h - 8) return len; len *= 0.85; } return 0; };
  // keep the anatomist's direction when it fits; otherwise swing it until a full-length arrow fits
  let best = { len: fit(dx, dy), ux: dx, uy: dy };
  if (best.len < want * 0.6) {
    for (const deg of [30, -30, 60, -60, 90, -90, 120, -120, 150, -150, 180]) {
      const r = deg * Math.PI / 180, ux = dx * Math.cos(r) - dy * Math.sin(r), uy = dx * Math.sin(r) + dy * Math.cos(r), len = fit(ux, uy);
      if (len > best.len) best = { len, ux, uy };
      if (len >= want * 0.6) break;
    }
  }
  return { x1: tx + best.ux * best.len, y1: ty + best.uy * best.len, x2: tx, y2: ty };
}
function drawArrow(svg, a, im, color) {
  const sw = Math.max(4, im.w / 170), hl = sw * 4.2, hw = sw * 2.6;
  const ang = Math.atan2(a.y2 - a.y1, a.x2 - a.x1), bx = a.x2 - Math.cos(ang) * hl, by = a.y2 - Math.sin(ang) * hl;
  const px = -Math.sin(ang) * hw, py = Math.cos(ang) * hw;
  const head = `${a.x2},${a.y2} ${bx + px},${by + py} ${bx - px},${by - py}`;
  svg.append(el('line', { x1: a.x1, y1: a.y1, x2: bx, y2: by, stroke: '#000', 'stroke-width': sw + 3, 'stroke-linecap': 'round', opacity: .7 }));
  svg.append(el('polygon', { points: head, fill: '#000', stroke: '#000', 'stroke-width': 3, opacity: .7 }));
  svg.append(el('line', { x1: a.x1, y1: a.y1, x2: bx, y2: by, stroke: color, 'stroke-width': sw, 'stroke-linecap': 'round' }));
  svg.append(el('polygon', { points: head, fill: color }));
}
function radiusFor(st, im) {
  const k = BANK.structs[st.s].kind;
  const f = (k === 'muscle' || k === 'bone') ? 0.085 : (k === 'space' || k === 'joint') ? 0.07 : 0.05;
  return Math.max(26, im.w * f);
}
// outline of the whole structure (tendon, belly, vessel) where one was drawn
function inPoly(pt, poly) {
  let c = false;
  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
    const [xi, yi] = poly[i], [xj, yj] = poly[j];
    if ((yi > pt[1]) !== (yj > pt[1]) && pt[0] < (xj - xi) * (pt[1] - yi) / (yj - yi) + xi) c = !c;
  }
  return c;
}
function polyDist(pt, rings) { return Math.min(...rings.map((r) => ringDist(pt, r))); }
function inRings(pt, rings) { return rings.some((r) => inPoly(pt, r)); }
function ringDist(pt, poly) {
  let m = Infinity;
  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
    const [ax, ay] = poly[j], [bx, by] = poly[i], dx = bx - ax, dy = by - ay, L = dx * dx + dy * dy || 1;
    const u = Math.max(0, Math.min(1, ((pt[0] - ax) * dx + (pt[1] - ay) * dy) / L));
    m = Math.min(m, Math.hypot(pt[0] - ax - u * dx, pt[1] - ay - u * dy));
  }
  return inPoly(pt, poly) ? 0 : m;
}
function pinGrade(st, im, p) {
  const d = (t) => Math.hypot(t[0] - p[0], t[1] - p[1]);
  const dT = Math.min(...st.tips.map(d));
  const P = POLY[st.id];
  if (P) {
    // on another labeled structure's outline?
    const o = (IMGST.get(st.img) || []).find((x) => x.s !== st.s && POLY[x.id] && inRings(p, POLY[x.id]));
    // anywhere on the outline counts; the old circle still counts too unless the pin sits on a different structure
    const ok = dT <= im.w * 0.025 || polyDist(p, P) <= im.w * 0.012 || (!o && dT <= radiusFor(st, im));
    return { ok, near: !ok && o ? BANK.structs[o.s].name : null };
  }
  let dO = Infinity, oName = null;
  (im.marks || []).forEach((m) => { if (m.s === st.s) return; const dd = d([m.x, m.y]); if (dd < dO) { dO = dd; oName = m.s ? BANK.structs[m.s].name : m.t; } });
  const R = radiusFor(st, im);
  const ok = dT <= im.w * 0.025 || (dT <= R && dT <= dO);
  return { ok, near: !ok && dO < dT && dO < R ? oName : null };
}

// ---------- quiz flow ----------
function show(v) { ['vSetup', 'vQuiz', 'vDone'].forEach((x) => { $(x).hidden = x !== v; }); document.body.classList.toggle('exam', v !== 'vSetup'); window.scrollTo(0, 0); }
// ---------- exam-skin chrome (hidden by CSS unless an exam skin is on) ----------
let flags = new Set();
// Review: vi is the index of an earlier station being looked at (read-only); null while on the live station.
let vi = null, live = null;
function renderPalette() {
  const pal = $('palette'); pal.innerHTML = '';
  queue.forEach((_, i) => { const b = document.createElement('span'); b.className = 'palette-btn'; b.textContent = i + 1; b.onclick = () => goTo(i); pal.append(b); });
}
function syncChrome() {
  const at = vi == null ? qi : vi, pal = $('palette').children;
  for (let i = 0; i < pal.length; i++) {
    const l = log[i]; pal[i].className = 'palette-btn' + (i === at ? ' current' : '') + (l ? (l.ok ? ' correct' : ' incorrect') : '') + (flags.has(i) ? ' flagged' : '') + (i <= qi ? ' reachable' : '');
  }
  if (pal[at]) pal[at].scrollIntoView({ block: 'nearest' });
  $('exNo').textContent = `Question ${at + 1}`;
  $('exFlag').classList.toggle('on', flags.has(at)); $('exFlag').textContent = flags.has(at) ? 'UNFLAG QUESTION' : 'FLAG QUESTION';
  $('exCount').textContent = vi == null ? `STATION ${qi + 1} OF ${queue.length}` : `REVIEWING STATION ${vi + 1} OF ${queue.length}`;
  $('exTitle').textContent = cfg.mode === 'hy' ? 'MSK Practical \u2014 High Yield' : 'MSK Practical';
  $('examfoot-next').textContent = vi != null ? (vi + 1 === qi ? 'Back to current' : 'Next') : !answered ? 'Submit' : qi + 1 >= queue.length ? 'Finish' : 'Next';
  $('examfoot-prev').disabled = at === 0; $('btnPrev').hidden = at === 0;
  $('btnBack').hidden = vi == null;
}
// ---------- review earlier stations (read-only) ----------
function showSnap(i) {
  const l = log[i], sn = l.snap, im = BANK.images[l.st.img];
  $('photo').src = 'img/' + l.st.img + (im.orig ? '.orig.jpg' : '.jpg'); showOrig = !!im.orig;
  const svg = $('ov'); svg.setAttribute('viewBox', `0 0 ${im.w} ${im.h}`); svg.innerHTML = sn.svg; svg.style.visibility = '';
  $('fig').classList.remove('pinning');
  $('cap').innerHTML = sn.cap; $('ctx').innerHTML = sn.ctx; $('ctx').hidden = !sn.ctx;
  $('qtype').innerHTML = sn.qtype; $('prompt').textContent = sn.prompt;
  $('ansForm').hidden = l.type === 'pin'; $('ans').value = sn.typed; $('ans').disabled = true;
  $('fb').innerHTML = sn.fb;
  $('btnSubmit').hidden = true; $('btnSkip').hidden = true; $('btnNext').hidden = true;
  $('btnOrig').hidden = !im.orig; $('btnOrig').textContent = im.orig ? 'Hide labels' : 'Show labeled original';
}
function goTo(i) {
  if (i < 0 || i > qi) return;
  if (i === qi) return backToLive();
  if (vi == null) { // leaving the live station: remember it and pause its timer
    clearInterval(tid);
    live = { typed: $('ans').value, pin, tleft };
  }
  vi = i; showSnap(i);
  $('qtype').innerHTML += ' <span class="rev">Review</span>'; $('btnNext').hidden = false;
  syncChrome();
}
function backToLive() {
  if (vi == null) return;
  vi = null;
  if (answered) { showSnap(qi); $('btnNext').hidden = false; }
  else {
    renderLive();
    if (live) {
      if (cur.type === 'pin') { pin = live.pin; if (pin) { drawPin(pin, '#38bdf8'); $('btnSubmit').disabled = false; } }
      else { $('ans').value = live.typed; setTimeout(() => $('ans').focus(), 30); }
      resumeTimer(live.tleft);
    }
  }
  live = null; syncChrome();
}
function stepPrev() { const at = vi == null ? qi : vi; if (at > 0) goTo(at - 1); }
function start(only) {
  queue = buildQueue(only); qi = 0; score = 0; log = []; flags = new Set();
  if (!queue.length) return;
  renderPalette();
  show('vQuiz'); ask();
}
function ask() {
  cur = queue[qi]; answered = false; pin = null; vi = null; live = null;
  const s = BANK.structs[cur.st.s];
  if (cur.type === 'rel') cur.rel = s.rel[cur.relIdx != null && s.rel[cur.relIdx] ? cur.relIdx : Math.floor(Math.random() * s.rel.length)];
  renderLive();
  startTimer();
}
function renderLive() {
  showOrig = false;
  const st = cur.st, im = BANK.images[st.img], s = BANK.structs[st.s];
  $('qn').textContent = qi + 1; $('qt').textContent = queue.length; $('qs').textContent = score;
  $('progBar').style.width = (100 * qi / queue.length) + '%';
  const photo = $('photo'); photo.src = 'img/' + st.img + '.jpg';
  const svg = $('ov'); svg.setAttribute('viewBox', `0 0 ${im.w} ${im.h}`); svg.innerHTML = ''; svg.style.visibility = '';
  $('fig').classList.toggle('pinning', cur.type === 'pin');
  const c = im.credit;
  $('cap').innerHTML = `Photo: ${esc(c.author)} &middot; <a href="${c.licenseUrl || '#'}" target="_blank" rel="noopener">${esc(c.license)}</a> &middot; <a href="${c.page}" target="_blank" rel="noopener">Wikimedia Commons</a> &middot; labels removed`;
  const unv = st.sure ? '' : ` <span class="unv" title="${esc(st.note || 'Label position or mapping was hard to confirm')}">unverified</span>`;
  const kw = KIND_WORD[s.kind] || 'structure';
  // orientation line for photos whose region isn't obvious; skipped if it happens to contain the answer
  let cx = CTX[st.img] || '';
  if (cx) { const nc = ' ' + norm(cx) + ' '; if ([s.name, ...(s.alts || [])].some((n) => { const w = norm(n); return w.length >= 4 && nc.includes(' ' + w + ' '); })) cx = ''; }
  $('ctx').innerHTML = cx ? '<b>Specimen:</b> ' + esc(cx) : ''; $('ctx').hidden = !cx;
  if (cur.type === 'pin') {
    $('qtype').innerHTML = 'Pin it' + unv;
    $('prompt').textContent = `Drop a pin on the ${s.name}.`;
    $('ansForm').hidden = true;
  } else {
    drawArrow(svg, arrowFor(st, im), im, '#facc15');
    $('qtype').innerHTML = (cur.type === 'rel' ? 'Second order' : 'Name it') + unv;
    $('prompt').textContent = cur.type === 'rel' ? cur.rel.q : `Name the indicated ${kw === 'bony structure' ? 'structure' : kw}.`;
    $('ansForm').hidden = false; $('ans').value = ''; $('ans').disabled = false;
    setTimeout(() => $('ans').focus(), 30);
  }
  $('btnSubmit').hidden = false; $('btnSkip').hidden = false; $('btnNext').hidden = true; $('btnOrig').hidden = true;
  $('btnSubmit').disabled = cur.type === 'pin';
  $('fb').innerHTML = '';
  syncChrome();
}
function startTimer() { resumeTimer(cfg.timer); }
function resumeTimer(left) {
  clearInterval(tid); const t = $('timer');
  if (!cfg.timer) { t.hidden = true; return; }
  tleft = left; t.hidden = false; tick();
  tid = setInterval(() => { tleft--; tick(); if (tleft <= 0) { clearInterval(tid); if (!answered) submit(true); } }, 1000);
}
function tick() { const t = $('timer'); t.textContent = `${Math.floor(tleft / 60)}:${String(Math.max(0, tleft) % 60).padStart(2, '0')}`; t.classList.toggle('low', tleft <= 10); }
function imgPoint(ev) {
  const r = $('photo').getBoundingClientRect(), im = BANK.images[cur.st.img];
  const sc = Math.min(r.width / im.w, r.height / im.h), ox = r.left + (r.width - im.w * sc) / 2, oy = r.top + (r.height - im.h * sc) / 2;
  const x = (ev.clientX - ox) / sc, y = (ev.clientY - oy) / sc;
  if (x < 0 || y < 0 || x > im.w || y > im.h) return null; return [x, y];
}
function drawPin(p, color) {
  const im = BANK.images[cur.st.img], r = Math.max(7, im.w / 85), svg = $('ov');
  svg.querySelectorAll('.pin').forEach((e) => e.remove());
  const g = el('g', { class: 'pin' });
  g.append(el('circle', { cx: p[0], cy: p[1], r: r + 3, fill: '#000', opacity: .55 }));
  g.append(el('circle', { cx: p[0], cy: p[1], r, fill: color, stroke: '#fff', 'stroke-width': Math.max(2, r / 3.5) }));
  svg.append(g);
}
function submit(timeout) {
  if (answered || !cur) return;
  const st = cur.st, s = BANK.structs[st.s], im = BANK.images[st.img];
  let ok = false, extra = '';
  if (cur.type === 'pin') {
    if (!pin && !timeout) return;
    if (pin) { const g = pinGrade(st, im, pin); ok = g.ok; if (g.near) extra = `Your pin is closer to the <b>${esc(g.near)}</b>.`; }
  } else {
    const typed = $('ans').value.trim();
    if (!typed && !timeout) return;
    ok = cur.type === 'rel' ? typedOk(typed, cur.rel.answers) : typedOk(typed, [s.name, ...(s.alts || [])]);
    $('ans').disabled = true;
  }
  finish(ok, extra, timeout);
}
function finish(ok, extra, timeout) {
  answered = true; clearInterval(tid);
  const st = cur.st, s = BANK.structs[st.s], im = BANK.images[st.img], svg = $('ov');
  if (ok) score++;
  log.push({ st, type: cur.type, ok, rel: cur.rel, relIdx: BANK.structs[st.s].rel ? BANK.structs[st.s].rel.indexOf(cur.rel) : null });
  $('qs').textContent = score;
  if (cur.type === 'pin') {
    const R = radiusFor(st, im), P = POLY[st.id];
    if (P) P.forEach((ring) => svg.append(el('polygon', { points: ring.map((q) => q.join(',')).join(' '), fill: 'rgba(34,197,94,.18)', stroke: '#22c55e', 'stroke-width': Math.max(2, im.w / 300), 'stroke-dasharray': '8 6', 'stroke-linejoin': 'round' })));
    else st.tips.forEach((t) => svg.append(el('circle', { cx: t[0], cy: t[1], r: R, fill: 'rgba(34,197,94,.18)', stroke: '#22c55e', 'stroke-width': Math.max(2, im.w / 300), 'stroke-dasharray': '8 6' })));
    st.tips.forEach((t) => svg.append(el('circle', { cx: t[0], cy: t[1], r: Math.max(4, im.w / 160), fill: '#22c55e' })));
    if (pin) drawPin(pin, ok ? '#22c55e' : '#ef4444');
  }
  let head, body;
  if (cur.type === 'rel') {
    head = ok ? 'Correct' : 'Not quite';
    body = `<div>Answer: <b>${esc(cur.rel.show || cur.rel.answers[0])}</b></div>` +
      (cur.rel.answers.length > 1 ? `<div class="alt">Also accepted: ${cur.rel.answers.filter((a) => a !== (cur.rel.show || cur.rel.answers[0])).map(esc).join('; ')}</div>` : '') +
      `<div class="alt">The indicated structure is the <b>${esc(s.name)}</b>.</div>` + (cur.rel.explain ? `<div class="ex">${esc(cur.rel.explain)}</div>` : '');
  } else {
    head = ok ? 'Correct' : (timeout ? "Time's up" : 'Not quite');
    body = `<div>${cur.type === 'pin' ? 'Target' : 'Answer'}: <b>${esc(s.name)}</b></div>` +
      (s.alts && s.alts.length ? `<div class="alt">Also accepted: ${s.alts.map(esc).join('; ')}</div>` : '') +
      (extra ? `<div class="alt">${extra}</div>` : '') + (cur.type === 'pin' ? `<div class="alt">The dashed ${POLY[st.id] ? 'outline' : 'circle'} shows the accepted area.</div>` : '') +
      (s.fact ? `<div class="ex">${esc(s.fact)}</div>` : '');
  }
  $('fb').innerHTML = `<div class="fb ${ok ? 'ok' : 'bad'}"><b class="v">${head}</b>${body}</div>`;
  $('btnSubmit').hidden = true; $('btnSkip').hidden = true; $('btnNext').hidden = false; $('btnOrig').hidden = !im.orig;
  if (im.orig) setOrig(true);
  // snapshot for review (Previous / station rail)
  log[log.length - 1].snap = { svg: svg.innerHTML, cap: $('cap').innerHTML, ctx: $('ctx').hidden ? '' : $('ctx').innerHTML, qtype: $('qtype').innerHTML,
    prompt: $('prompt').textContent, typed: $('ans').value, fb: $('fb').innerHTML };
  $('btnNext').focus();
  syncChrome();
}
function next() {
  if (vi != null) return vi + 1 === qi ? backToLive() : goTo(vi + 1);
  if (!answered) return;
  qi++; if (qi >= queue.length) return end();
  ask();
}
function end() {
  clearInterval(tid); show('vDone');
  const n = log.length, pct = n ? Math.round(100 * score / n) : 0;
  $('final').innerHTML = `${score} / ${n}<small>${pct}% correct</small>`;
  const miss = log.filter((l) => !l.ok); const box = $('missed'); box.innerHTML = '';
  $('missedWrap').hidden = !miss.length; $('btnRetry').hidden = !miss.length;
  const fl = [...flags].sort((a, b) => a - b).map((i) => log[i]).filter(Boolean); $('flagWrap').hidden = !fl.length; $('flagged').innerHTML = '';
  fl.forEach((l) => { const s = BANK.structs[l.st.s]; const d = document.createElement('div'); d.className = 'mcard';
    d.innerHTML = `<img src="img/${l.st.img}.jpg" alt="" loading="lazy"><div><b>${esc(s.name)}</b><i>${l.ok ? 'Correct' : 'Missed'} &middot; ${l.type === 'pin' ? 'Pin it' : l.type === 'rel' ? esc(l.rel.q) : 'Name it'}</i></div>`; $('flagged').append(d); });
  miss.forEach((l) => {
    const s = BANK.structs[l.st.s];
    const d = document.createElement('div'); d.className = 'mcard';
    d.innerHTML = `<img src="img/${l.st.img}.jpg" alt="" loading="lazy"><div><b>${esc(s.name)}</b><i>${l.type === 'pin' ? 'Pin it' : l.type === 'rel' ? esc(l.rel.q) + ' → ' + esc(l.rel.show || l.rel.answers[0]) : 'Name it'}</i></div>`;
    box.append(d);
  });
}
function esc(s) { return String(s == null ? '' : s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c])); }

// ---------- wiring ----------
$('btnStart').onclick = () => start();
$('optRel').onchange = (e) => { cfg.rel = e.target.checked; saveCfg(); };
$('optUnv').onchange = (e) => { cfg.unv = e.target.checked; saveCfg(); renderSetup(); };
$('ansForm').onsubmit = (e) => { e.preventDefault(); if (answered) next(); else submit(); };
$('btnSubmit').onclick = () => submit();
$('btnSkip').onclick = () => { if (!answered) finish(false, '', false); };
$('btnNext').onclick = next;
$('exFlag').onclick = () => { if (flags.has(qi)) flags.delete(qi); else flags.add(qi); syncChrome(); };
$('examfoot-next').onclick = () => { if (vi != null || answered) next(); else if (cur.type !== 'pin' || pin) submit(); };
$('examfoot-prev').onclick = stepPrev; $('btnPrev').onclick = stepPrev; $('btnBack').onclick = backToLive;
$('btnQuit').onclick = () => { if (log.length) end(); else { clearInterval(tid); show('vSetup'); } };
$('btnAgain').onclick = () => { show('vSetup'); renderSetup(); };
$('btnRetry').onclick = () => { const miss = log.filter((l) => !l.ok).map((l) => Object.assign({}, l.st, { qtype: l.type, qrel: l.relIdx >= 0 ? l.relIdx : null })); start(miss); };
// The labeled original is the same size as the cleaned photo, so the arrow, pin and accepted area stay on top of it.
function setOrig(on) {
  showOrig = on;
  $('photo').src = 'img/' + (vi == null ? cur.st : log[vi].st).img + (on ? '.orig.jpg' : '.jpg');
  $('btnOrig').textContent = on ? 'Hide labels' : 'Show labeled original';
}
$('btnOrig').onclick = () => setOrig(!showOrig);
$('fig').addEventListener('click', (ev) => {
  if (!cur || cur.type !== 'pin' || answered || vi != null) return;
  const p = imgPoint(ev); if (!p) return; pin = p; drawPin(p, '#38bdf8'); $('btnSubmit').disabled = false;
});
document.addEventListener('keydown', (e) => {
  if (e.key !== 'Enter' || $('vQuiz').hidden) return;
  if (vi != null) { e.preventDefault(); next(); return; }
  if (e.target && e.target.id === 'ans') return;           // handled by the form
  if (e.target && e.target.tagName === 'BUTTON' && e.target.id !== 'btnNext') return;
  e.preventDefault();
  if (answered) next(); else if (cur && cur.type === 'pin' && pin) submit();
});

Promise.all([fetch('data/bank.json?v=5').then((r) => r.json()), fetch('data/hy.json?v=5').then((r) => (r.ok ? r.json() : [])).catch(() => []), fetch('data/ctx.json?v=5').then((r) => (r.ok ? r.json() : {})).catch(() => ({})), fetch('data/poly.json?v=10').then((r) => (r.ok ? r.json() : {})).catch(() => ({}))]).then(([b, hy, ctx, poly]) => {
  BANK = b; HY = hy || []; CTX = ctx || {}; POLY = {};
  // an outline is one ring [[x,y],...] or, for a structure seen in separate parts, a list of rings
  Object.entries(poly || {}).forEach(([k, v]) => { if (v && v.length) POLY[k] = typeof v[0][0] === 'number' ? [v] : v; });
  b.stations.forEach((s) => { if (!IMGST.has(s.img)) IMGST.set(s.img, []); IMGST.get(s.img).push(s); }); BYID = new Map(b.stations.map((s) => [s.id, s]));
  if (cfg.mode === 'hy' && !HY.length) cfg.mode = 'all';
  cfg.regions = cfg.regions.filter((r) => BANK.regions.some((x) => x.id === r));
  if (cfg.mode === 'all') cfg.mode = 'hy'; // until the sign-in check says otherwise
  renderSetup();
  if (window.ATSkin) {
    ATSkin.renderPicker($('skin-picker'));
    ATSkin.access((a) => { FULL = a; if (a === 'ok') cfg.mode = (LS.get('mskp_cfg', {}).mode) || cfg.mode; renderSetup(); });
  } else { FULL = 'error'; renderSetup(); }
}).catch(() => { $('pool').textContent = 'Could not load the question bank.'; });
