"use strict";
// Paris Walk – follow one stage of the "every street" circuit.
// Progress is tracked as distance along the route (not "nearest line"), so a
// street walked out and back is never confused with its return leg.

const AHEAD_M = 300;        // bold part of the route
const PREVIEW_M = 1200;     // faint dashed part after it
const ON_ROUTE_M = 30;      // GPS fix within this distance = on route
const ALERT_M = 30;         // vibrate this far before a turn / U-turn
const MAX_SPEED = 3;       // m/s, fastest plausible walking pace
const LAT0 = 48.86, KX = 111320 * Math.cos(LAT0 * Math.PI / 180), KY = 110540;

const $ = id => document.getElementById(id);
const store = {
  get(k, def) { try { const v = localStorage.getItem("pw:" + k); return v === null ? def : JSON.parse(v); } catch { return def; } },
  set(k, v) { try { localStorage.setItem("pw:" + k, JSON.stringify(v)); } catch {} },
};
const fmtD = m => m >= 1000 ? (m / 1000).toFixed(m >= 10000 ? 0 : 1) + " km" : Math.round(m / 10) * 10 + " m";

// ---------- map
const map = L.map("map", { zoomControl: false, attributionControl: true }).setView([48.857, 2.342], 13);
L.tileLayer("https://tile.openstreetmap.org/{z}/{x}/{y}.png", {
  maxZoom: 19, attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a>',
}).addTo(map);
const lyr = {
  walked: L.polyline([], { color: "#8e8e93", weight: 4, opacity: .55 }).addTo(map),
  preview: L.polyline([], { color: "#e6194b", weight: 3, opacity: .45, dashArray: "2 8" }).addTo(map),
  casing: L.polyline([], { color: "#fff", weight: 11, opacity: .9 }).addTo(map),
  ahead: L.polyline([], { color: "#e6194b", weight: 7, opacity: 1 }).addTo(map),
  marks: L.layerGroup().addTo(map),
  ends: L.layerGroup().addTo(map),
};
const me = L.marker([0, 0], { icon: L.divIcon({ className: "", html: '<div class="me"></div>', iconSize: [18, 18] }), zIndexOffset: 1000 });

// ---------- state
let INDEX = null, S = null;          // stage list, current stage
let s = 0;                           // progress along the stage (m)
let follow = true, tracking = false, watchId = null, offCount = 0, alerted = new Set();
let simMult = 0, simTimer = null, simS = 0, wakeLock = null, lastSave = 0, lastFix = null, lastOnRoute = 0;

// ---------- geometry helpers
function prepare(st) {
  const n = st.pts.length, x = new Float64Array(n), y = new Float64Array(n), d = new Float64Array(n);
  for (let i = 0; i < n; i++) {
    x[i] = (st.pts[i][1] - 2.35) * KX; y[i] = (st.pts[i][0] - LAT0) * KY;
    if (i) d[i] = d[i - 1] + Math.hypot(x[i] - x[i - 1], y[i] - y[i - 1]);
  }
  Object.assign(st, { x, y, d, total: d[n - 1] });
  st.uturnD = st.uturns.map(i => d[i]);
  st.nameD = st.names.map(([i, nm]) => [d[i], nm]);
  st.newD = st.new.map(([i, f]) => [d[i], f]);
  return st;
}
function seg(dd) {            // index i with d[i] <= dd < d[i+1]
  const d = S.d; let lo = 0, hi = d.length - 2;
  if (dd <= 0) return 0; if (dd >= S.total) return hi;
  while (lo < hi) { const m = (lo + hi + 1) >> 1; if (d[m] <= dd) lo = m; else hi = m - 1; }
  return lo;
}
function at(dd) {             // {lat, lon, x, y} at distance dd
  dd = Math.max(0, Math.min(S.total, dd));
  const i = seg(dd), L = S.d[i + 1] - S.d[i], t = L > 0 ? (dd - S.d[i]) / L : 0, p = S.pts[i], q = S.pts[i + 1];
  return { lat: p[0] + (q[0] - p[0]) * t, lon: p[1] + (q[1] - p[1]) * t,
           x: S.x[i] + (S.x[i + 1] - S.x[i]) * t, y: S.y[i] + (S.y[i + 1] - S.y[i]) * t };
}
function slice(a, b) {
  a = Math.max(0, a); b = Math.min(S.total, b);
  if (b <= a) return [];
  const out = [[at(a).lat, at(a).lon]];
  for (let i = seg(a) + 1; i < S.pts.length && S.d[i] < b; i++) out.push(S.pts[i]);
  const e = at(b); out.push([e.lat, e.lon]);
  return out;
}
function bearing(a, b) { const p = at(a), q = at(b); return Math.atan2(q.x - p.x, q.y - p.y) * 180 / Math.PI; }
function runAt(runs, dd) { let r = runs[0]; for (const x of runs) { if (x[0] <= dd + .01) r = x; else break; } return r; }

// project a fix on the route between distances lo..hi; returns sorted candidates
function project(px, py, lo, hi) {
  const out = [];
  for (let i = seg(Math.max(0, lo)); i < S.pts.length - 1 && S.d[i] <= hi; i++) {
    const ax = S.x[i], ay = S.y[i], dx = S.x[i + 1] - ax, dy = S.y[i + 1] - ay, L2 = dx * dx + dy * dy;
    const t = L2 ? Math.max(0, Math.min(1, ((px - ax) * dx + (py - ay) * dy) / L2)) : 0;
    const along = S.d[i] + t * (S.d[i + 1] - S.d[i]);
    if (along < lo || along > hi) continue;
    out.push({ dist: Math.hypot(px - ax - t * dx, py - ay - t * dy), along });
  }
  return out;
}

// ---------- GPS fix handling
function onFix(lat, lon, acc) {
  if (!S) return;
  lastFix = { lat, lon };
  me.setLatLng([lat, lon]).addTo(map);
  if (acc > 50) { render(); return; }
  const now = Date.now(), dt = lastOnRoute ? (now - lastOnRoute) / 1000 : 60;
  if (advance((lon - 2.35) * KX, (lat - LAT0) * KY, dt, acc)) lastOnRoute = now;
  else if (offCount === 3) { buzz([300, 150, 300]); toast("Off route"); }
  save();
  render();
}

// ---------- position filter
// Progress is one number (metres along the stage), so we keep a probability for
// every GRID-metre cell of the route (a 1-D Bayes / HMM filter). At each fix:
//  1. predict: you moved forward between 0 and MAX_SPEED*dt metres (a little
//     backward is allowed, less likely);
//  2. update: cells close to the GPS fix get more weight (Gaussian, sigma = accuracy).
// Both legs of an out-and-back stay possible until continuity settles it, and a
// loop that passes next to itself is out of reach of the prediction.
const GRID = 2, BACK_CELLS = 3, BACK_W = 0.3;
let P = null, pLo = 0, pHi = 0;                  // belief and its non-zero range (cells)

function cells() {
  if (S.cx) return;
  const n = Math.floor(S.total / GRID) + 1;
  S.cx = new Float32Array(n); S.cy = new Float32Array(n);
  for (let j = 0; j < n; j++) { const p = at(j * GRID); S.cx[j] = p.x; S.cy[j] = p.y; }
}
function resetBelief(at_m) {
  cells();
  P = new Float64Array(S.cx.length);
  const j = Math.max(0, Math.min(P.length - 1, Math.round(at_m / GRID)));
  P[j] = 1; pLo = pHi = j;
}

function advance(px, py, dt, acc = 10) {
  const n = P.length, mult = simTimer ? Math.max(1, simMult) : 1;
  const fwd = Math.max(2, Math.min(Math.ceil(MAX_SPEED * mult * Math.max(dt, 1) / GRID), Math.ceil(1500 / GRID)));
  const lo = Math.max(0, pLo - BACK_CELLS), hi = Math.min(n - 1, pHi + fwd);
  // 1. predict: Q[j] = sum P[i] for j-fwd <= i <= j (forward) + BACK_W * (j < i <= j+BACK)
  const C = new Float64Array(hi - lo + 2);       // prefix sums of P over [lo, hi]
  for (let j = lo; j <= hi; j++) C[j - lo + 1] = C[j - lo] + P[j];
  const sum = (a, b) => (a = Math.max(a, lo), b = Math.min(b, hi), b < a ? 0 : C[b - lo + 1] - C[a - lo]);
  const sig2 = 2 * Math.max(6, Math.min(acc, 30)) ** 2;
  const Q = new Float64Array(hi - lo + 1);
  let best = Infinity, tot = 0;
  for (let j = lo; j <= hi; j++) {
    const prior = sum(j - fwd, j) / (fwd + 1) + BACK_W * sum(j + 1, j + BACK_CELLS) / BACK_CELLS;
    if (prior <= 0) continue;
    const d2 = (S.cx[j] - px) ** 2 + (S.cy[j] - py) ** 2;
    best = Math.min(best, d2);
    tot += Q[j - lo] = prior * Math.exp(-d2 / sig2);
  }
  if (Math.sqrt(best) > ON_ROUTE_M || !(tot > 0)) { offCount++; return false; }
  // 2. normalise, prune tiny cells, take the most likely cell as progress
  P.fill(0, pLo, pHi + 1);
  let mx = 0, arg = lo; pLo = hi; pHi = lo;
  for (let j = lo; j <= hi; j++) { const v = Q[j - lo] / tot; if (v > mx) { mx = v; arg = j; } }
  for (let j = lo; j <= hi; j++) {
    const v = Q[j - lo] / tot;
    if (v > mx * 1e-4) { P[j] = v; pLo = Math.min(pLo, j); pHi = Math.max(pHi, j); }
  }
  s = Math.min(S.total, arg * GRID);
  offCount = 0;
  return true;
}

function relocate() {          // jump to the nearest point anywhere on the stage
  if (!S || !lastFix) { toast("No GPS position yet"); return; }
  const px = (lastFix.lon - 2.35) * KX, py = (lastFix.lat - LAT0) * KY;
  const c = project(px, py, 0, S.total), best = Math.min(...c.map(o => o.dist));
  const near = c.filter(o => o.dist <= best + 8);
  const ahead = near.filter(o => o.along >= s);
  s = (ahead.length ? ahead : near).reduce((m, o) => o.along < m.along ? o : m).along;
  offCount = 0; lastOnRoute = 0; resetBelief(s); alerted.clear(); simS = s; save(true); render(); toast("Position updated");
}

function save(force) {
  const now = Date.now();
  if (!force && now - lastSave < 5000) return;
  lastSave = now;
  store.set("s:" + S.n, Math.max(Math.round(s), store.get("s:" + S.n, 0)));
  if (s >= S.total - 25) store.set("done:" + S.n, true);
}

// ---------- guidance
function guidance() {
  const cur = runAt(S.nameD, s)[1];
  let ev = null;
  const nx = S.nameD.find(([dd]) => dd > s + 1);
  if (nx) {
    const delta = ((bearing(nx[0], nx[0] + 12) - bearing(nx[0] - 12, nx[0]) + 540) % 360) - 180;
    const a = Math.abs(delta);
    const [icon, verb] = a < 25 ? ["↑", "Continue onto"] : a < 60 ? [delta > 0 ? "↗" : "↖", delta > 0 ? "Bear right onto" : "Bear left onto"]
      : a < 150 ? [delta > 0 ? "→" : "←", delta > 0 ? "Turn right onto" : "Turn left onto"] : ["↶", "Turn back onto"];
    ev = { at: nx[0], icon, text: `${verb} ${nx[1]}`, cls: a >= 150 ? "uturn" : "" };
  }
  const ut = S.uturnD.find(dd => dd > s + 1);
  if (ut !== undefined && (!ev || ut <= ev.at + 15)) ev = { at: ut, icon: "↶", text: `Turn back along ${cur}`, cls: "uturn" };
  return { cur, ev };
}

// ---------- render
function render() {
  if (!S) return;
  lyr.walked.setLatLngs(slice(0, s));
  const ah = slice(s, s + AHEAD_M);
  lyr.ahead.setLatLngs(ah); lyr.casing.setLatLngs(ah);
  lyr.preview.setLatLngs(slice(s + AHEAD_M, s + AHEAD_M + PREVIEW_M));
  lyr.marks.clearLayers();
  for (let dd = s + 25; dd < Math.min(S.total, s + AHEAD_M); dd += 40) {
    const p = at(dd), b = bearing(dd - 2, dd + 2);
    L.marker([p.lat, p.lon], { interactive: false, icon: L.divIcon({ className: "arrow", iconSize: [16, 16],
      html: `<div style="transform:rotate(${b}deg)">▲</div>` }) }).addTo(lyr.marks);
  }
  for (const dd of S.uturnD) if (dd > s && dd < s + AHEAD_M + PREVIEW_M) {
    const p = at(dd);
    L.circleMarker([p.lat, p.lon], { radius: 7, color: "#fff", weight: 2, fillColor: "#d97706", fillOpacity: 1 })
      .bindTooltip("U-turn").addTo(lyr.marks);
  }

  const done = s >= S.total - 25;
  const { cur, ev } = guidance();
  const gi = $("gicon");
  if (done) {
    gi.textContent = "✓"; gi.className = ""; $("gdist").textContent = "Stage complete";
    $("gwhat").textContent = `Metro ${S.to}`; $("gnow").textContent = "";
  } else if (offCount >= 3) {
    gi.textContent = "?"; gi.className = "off"; $("gdist").textContent = "Off route";
    $("gwhat").textContent = "Walk back to the red line, or tap ⋯ → Re-locate"; $("gnow").textContent = cur;
  } else if (ev) {
    const dist = ev.at - s;
    gi.textContent = dist > 1000 ? "↑" : ev.icon; gi.className = dist > 1000 ? "" : ev.cls;
    $("gdist").textContent = dist > 1000 ? `Continue ${fmtD(dist)}` : fmtD(dist);
    $("gwhat").textContent = ev.text; $("gnow").textContent = "On " + cur;
    const id = Math.round(ev.at);
    if (tracking && dist <= ALERT_M && !alerted.has(id)) {
      alerted.add(id);
      buzz(ev.cls === "uturn" ? [200, 100, 200, 100, 200] : [180]);
    }
  } else {
    gi.textContent = "↑"; gi.className = ""; $("gdist").textContent = fmtD(S.total - s);
    $("gwhat").textContent = `To the end · Metro ${S.to}`; $("gnow").textContent = "On " + cur;
  }
  $("bstage").innerHTML = `<b>Stage ${S.n}</b> · ${S.from} → ${S.to}`;
  $("bkm").innerHTML = `<b>${(s / S.total * S.km).toFixed(1)}</b> / ${S.km.toFixed(1)} km`;   // route km (offset line is a bit longer)
  document.querySelector("#prog i").style.width = (100 * s / S.total) + "%";
  if (follow) {
    const p = lastFix && tracking ? lastFix : at(s);
    map.setView([p.lat, p.lon], Math.max(map.getZoom(), 17), { animate: false });
  }
}

// ---------- tracking
async function startTracking() {
  tracking = true; $("bgo").textContent = "Pause"; follow = true;
  try { wakeLock = await navigator.wakeLock?.request("screen"); } catch {}
  if (simMult) startSim();
  else if (!("geolocation" in navigator) || !window.isSecureContext) toast("GPS needs https – use ⋯ → Simulate");
  else watchId = navigator.geolocation.watchPosition(
    p => onFix(p.coords.latitude, p.coords.longitude, p.coords.accuracy),
    e => toast("GPS: " + e.message), { enableHighAccuracy: true, maximumAge: 2000, timeout: 20000 });
  render();
}
function stopTracking() {
  tracking = false; $("bgo").textContent = "Resume";
  if (watchId !== null) navigator.geolocation.clearWatch(watchId); watchId = null;
  clearInterval(simTimer); simTimer = null;
  wakeLock?.release?.(); wakeLock = null;
  if (S) save(true);
}
document.addEventListener("visibilitychange", async () => {
  if (tracking && document.visibilityState === "visible" && !wakeLock) try { wakeLock = await navigator.wakeLock?.request("screen"); } catch {}
});

function startSim() {
  clearInterval(simTimer);
  simS = s;
  simTimer = setInterval(() => {
    simS = Math.min(S.total, simS + 1.4 * simMult);
    const p = at(simS), r = () => (Math.random() - .5) * 8;   // ±4 m GPS noise
    onFix(p.lat + r() / KY, p.lon + r() / KX, 6);
    if (simS >= S.total) clearInterval(simTimer);
  }, 1000);
}

// ---------- stages
async function openStage(n) {
  const r = await fetch(`data/stage_${String(n).padStart(3, "0")}.json`);
  S = prepare(await r.json());
  s = Math.min(store.get("s:" + n, 0), S.total);
  store.set("cur", n); alerted.clear(); offCount = 0; lastOnRoute = 0; resetBelief(s);
  for (const l of ["ahead", "preview"]) lyr[l].setStyle({ color: S.c });
  lyr.ends.clearLayers();
  const a = S.pts[0], b = S.pts[S.pts.length - 1];
  L.circleMarker(a, { radius: 8, color: "#fff", weight: 3, fillColor: "#2e9e44", fillOpacity: 1 }).bindTooltip(`Start · Metro ${S.from}`).addTo(lyr.ends);
  L.circleMarker(b, { radius: 8, color: "#fff", weight: 3, fillColor: "#111", fillOpacity: 1 }).bindTooltip(`End · Metro ${S.to}`).addTo(lyr.ends);
  $("bgo").textContent = s > 0 ? "Resume" : "Start";
  follow = true; render();
}

function buildList() {
  let walked = 0, done = 0;
  $("list").innerHTML = INDEX.stages.map(st => {
    const p = store.get("s:" + st.n, 0) / 1000, ok = store.get("done:" + st.n, false);
    walked += ok ? st.km : p; done += ok ? 1 : 0;
    const pill = ok ? '<span class="pill done">Done</span>' : p > 0 ? `<span class="pill">${p.toFixed(1)} / ${st.km.toFixed(1)} km</span>`
      : `<span class="pill">${st.km.toFixed(1)} km</span>`;
    return `<div class="st${S && S.n === st.n ? " cur" : ""}" data-n="${st.n}"><span class="sw" style="background:${st.c}"></span>
      <div class="t"><div><b>Stage ${st.n}</b></div><div><small>${st.from} → ${st.to}</small></div></div>${pill}</div>`;
  }).join("");
  const tot = INDEX.stages.reduce((a, st) => a + st.km, 0);
  $("total").textContent = `${walked.toFixed(1)} of ${tot.toFixed(0)} km walked · ${done} of ${INDEX.stages.length} stages done`;
}

// ---------- UI
function toast(t) { const e = $("toast"); e.textContent = t; e.style.display = "block"; clearTimeout(toast.t); toast.t = setTimeout(() => e.style.display = "none", 2500); }
function buzz(p) { try { navigator.vibrate?.(p); } catch {} }

$("bgo").onclick = () => S ? (tracking ? stopTracking() : startTracking()) : $("bstages").onclick();
$("bstages").onclick = () => { buildList(); $("panel").classList.add("open"); document.querySelector(".st.cur")?.scrollIntoView({ block: "center" }); };
$("pclose").onclick = () => $("panel").classList.remove("open");
$("list").onclick = e => {
  const el = e.target.closest(".st"); if (!el) return;
  if (tracking) stopTracking();
  $("panel").classList.remove("open"); openStage(+el.dataset.n);
};
$("bmore").onclick = () => { $("sim").classList.toggle("show"); placeRecenter(); };
function placeRecenter() { $("recenter").style.bottom = ($("bar").getBoundingClientRect().height + 22) + "px"; }
window.addEventListener("resize", placeRecenter); placeRecenter();
$("sim").querySelectorAll("[data-x]").forEach(b => b.onclick = () => {
  simMult = +b.dataset.x;
  $("sim").querySelectorAll("[data-x]").forEach(o => o.classList.toggle("on", o === b));
  if (tracking) { stopTracking(); startTracking(); }
});
$("relocate").onclick = relocate;
$("recenter").onclick = () => { follow = true; render(); };
map.on("dragstart", () => { follow = false; });

(async () => {
  INDEX = await (await fetch("data/index.json")).json();
  const cur = store.get("cur", null);
  if (cur) openStage(cur); else { buildList(); $("panel").classList.add("open"); }
  if ("serviceWorker" in navigator && window.isSecureContext) navigator.serviceWorker.register("sw.js").catch(() => {});
})();
