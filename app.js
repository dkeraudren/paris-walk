"use strict";
// Paris Walk – follow the whole "every street" circuit as one continuous route.
// Stop whenever you like; the app resumes where you left off.
// Progress is tracked as distance along the route (not "nearest line"), so a
// street walked out and back is never confused with its return leg.

const AHEAD_M = 300;        // bold part of the route
const PREVIEW_M = 1200;     // faint dashed part after it
const WALKED_M = 3000;      // grey "already walked" trail shown behind you
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
let S = null;                        // the route
let s = 0;                           // progress along the route (m)
let follow = true, tracking = false, watchId = null, offCount = 0, alerted = new Set();
let simMode = false, simMult = 1, simTimer = null, simS = 0, simDetour = null, simBad = false, wakeLock = null, lastSave = 0, lastFix = null, lastOnRoute = 0;

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
  st.stopD = st.stops.map(([i, nm]) => [d[i], nm]);
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
function upper(arr, v, key = x => x) {   // first index with key(arr[i]) > v
  let lo = 0, hi = arr.length;
  while (lo < hi) { const m = (lo + hi) >> 1; if (key(arr[m]) > v) hi = m; else lo = m + 1; }
  return lo;
}
function runAt(runs, dd) { return runs[Math.max(0, upper(runs, dd + .01, r => r[0]) - 1)]; }

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
  for (let j = 0, i = 0; j < n; j++) {
    const dd = Math.min(j * GRID, S.total);
    while (i < S.d.length - 2 && S.d[i + 1] <= dd) i++;
    const L = S.d[i + 1] - S.d[i], t = L > 0 ? (dd - S.d[i]) / L : 0;
    S.cx[j] = S.x[i] + (S.x[i + 1] - S.x[i]) * t; S.cy[j] = S.y[i] + (S.y[i + 1] - S.y[i]) * t;
  }
  P = new Float64Array(n);
}
function resetBelief(at_m) {
  cells();
  P.fill(0, pLo, pHi + 1);
  const j = Math.max(0, Math.min(P.length - 1, Math.round(at_m / GRID)));
  P[j] = 1; pLo = pHi = j;
}

function advance(px, py, dt, acc = 10) {
  const n = P.length, mult = simMode ? simMult : 1;
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

function relocate() {          // jump to the next time the route passes here
  if (!S || !lastFix) { toast("No GPS position yet"); return; }
  const px = (lastFix.lon - 2.35) * KX, py = (lastFix.lat - LAT0) * KY;
  const c = project(px, py, 0, S.total), best = c.reduce((m, o) => Math.min(m, o.dist), Infinity);
  const near = c.filter(o => o.dist <= best + 8);
  const prev = s;
  const ahead = near.filter(o => o.along >= s - 50);
  s = (ahead.length ? ahead : near).reduce((m, o) => o.along < m.along ? o : m).along;
  const t = store.get("today", null), jump = s - prev;       // a jump is not "walked today"
  if (t && t.day === today()) store.set("today", { day: t.day, from: t.from + jump });
  offCount = 0; lastOnRoute = 0; resetBelief(s); alerted.clear(); simS = s; save(true); render(); toast("Position updated");
}

function save(force) {
  if (simMode) return;                 // a simulated walk never touches real progress
  const now = Date.now();
  if (!force && now - lastSave < 5000) return;
  lastSave = now;
  store.set("pos", Math.round(s));
  const day = today(), t = store.get("today", null);
  if (!t || t.day !== day) store.set("today", { day, from: Math.round(s) });
}

// ---------- guidance
function guidance() {
  const cur = runAt(S.nameD, s)[1];
  let ev = null;
  const nx = S.nameD[upper(S.nameD, s + 1, r => r[0])];
  if (nx) {
    const delta = ((bearing(nx[0], nx[0] + 12) - bearing(nx[0] - 12, nx[0]) + 540) % 360) - 180;
    const a = Math.abs(delta);
    const [icon, verb] = a < 25 ? ["↑", "Continue onto"] : a < 60 ? [delta > 0 ? "↗" : "↖", delta > 0 ? "Bear right onto" : "Bear left onto"]
      : a < 150 ? [delta > 0 ? "→" : "←", delta > 0 ? "Turn right onto" : "Turn left onto"] : ["↶", "Turn back onto"];
    ev = { at: nx[0], icon, text: `${verb} ${nx[1]}`, cls: a >= 150 ? "uturn" : "" };
  }
  const ut = S.uturnD[upper(S.uturnD, s + 1)];
  if (ut !== undefined && (!ev || ut <= ev.at + 15)) ev = { at: ut, icon: "↶", text: `Turn back along ${cur}`, cls: "uturn" };
  return { cur, ev };
}

// ---------- render
function render() {
  if (!S) return;
  lyr.walked.setLatLngs(slice(s - WALKED_M, s));
  const ah = slice(s, s + AHEAD_M);
  lyr.ahead.setLatLngs(ah); lyr.casing.setLatLngs(ah);
  lyr.preview.setLatLngs(slice(s + AHEAD_M, s + AHEAD_M + PREVIEW_M));
  lyr.marks.clearLayers();
  for (let dd = s + 25; dd < Math.min(S.total, s + AHEAD_M); dd += 40) {
    const p = at(dd), b = bearing(dd - 2, dd + 2);
    L.marker([p.lat, p.lon], { interactive: false, icon: L.divIcon({ className: "arrow", iconSize: [16, 16],
      html: `<div style="transform:rotate(${b}deg)">▲</div>` }) }).addTo(lyr.marks);
  }
  for (let k = upper(S.uturnD, s); k < S.uturnD.length && S.uturnD[k] < s + AHEAD_M + PREVIEW_M; k++) {
    const dd = S.uturnD[k];
    const p = at(dd);
    L.circleMarker([p.lat, p.lon], { radius: 7, color: "#fff", weight: 2, fillColor: "#d97706", fillOpacity: 1 })
      .bindTooltip("U-turn").addTo(lyr.marks);
  }

  const done = s >= S.total - 25;
  const { cur, ev } = guidance();
  const gi = $("gicon");
  if (done) {
    gi.textContent = "✓"; gi.className = ""; $("gdist").textContent = "Every street walked!";
    $("gwhat").textContent = "Paris is done."; $("gnow").textContent = "";
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
    $("gwhat").textContent = "To the end"; $("gnow").textContent = "On " + cur;
  }
  const km = m => m / S.total * S.km;            // route km (the offset line is a bit longer)
  const t = store.get("today", null), from = t && t.day === today() ? t.from : s;
  $("bkm").innerHTML = `<b>${km(s).toFixed(1)}</b> / ${Math.round(S.km).toLocaleString("en")} km · ${(100 * s / S.total).toFixed(1)}%`;
  $("btoday").innerHTML = `Today <b>${km(Math.max(0, s - from)).toFixed(1)} km</b>`;
  const stop = S.stopD[upper(S.stopD, s + 30, r => r[0])];
  $("bnext").innerHTML = stop ? `Good place to stop: <b>Metro ${stop[1]}</b> in ${fmtD(stop[0] - s)}` : "";
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
  if (simMode) startSim();
  else if (!("geolocation" in navigator) || !window.isSecureContext) toast("GPS needs https – try Simulate");
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
function today() { const d = new Date(); return d.getFullYear() + "-" + (d.getMonth() + 1) + "-" + d.getDate(); }
document.addEventListener("visibilitychange", async () => {
  if (tracking && document.visibilityState === "visible" && !wakeLock) try { wakeLock = await navigator.wakeLock?.request("screen"); } catch {}
});

// ---------- simulation: a virtual walker follows the route and sends fake GPS fixes
// once a second. "Wrong turn" walks it 80 m off the route and back; "Bad GPS" adds
// city-canyon noise and the odd wild fix. Real progress is restored on exit.
function startSim() {
  clearInterval(simTimer);
  simS = Math.max(simS, s);
  simTimer = setInterval(simStep, 1000);
}
function simStep() {
  const step = 1.4 * simMult;                    // 1.4 m/s = 5 km/h
  let p;
  if (simDetour) {                               // walking away from the route, then back
    const d = simDetour;
    if (d.phase === "out") { d.off += Math.min(step, 12); if (d.off >= 80) { d.off = 80; d.phase = "wait"; d.wait = 4; } }
    else if (d.phase === "wait") { if (--d.wait <= 0) d.phase = "back"; }
    else { d.off -= Math.min(step, 12); if (d.off <= 0) simDetour = null; }
    const b = at(simS);
    p = { x: b.x + d.nx * (simDetour ? d.off : 0), y: b.y + d.ny * (simDetour ? d.off : 0) };
  } else {
    simS = Math.min(S.total, simS + step);
    p = at(simS);
  }
  let noise = 4, acc = 6;
  if (simBad) { noise = 15; acc = 25; if (Math.random() < .08) { noise = 70; acc = 40; } }
  const r = () => (Math.random() - .5) * 2 * noise;
  const x = p.x + r(), y = p.y + r();
  onFix(y / KY + LAT0, x / KX + 2.35, acc);
  if (simS >= S.total) clearInterval(simTimer);
}
function enterSim() {
  if (tracking) stopTracking();
  simMode = true; simS = s; simDetour = null;
  $("bar").classList.add("simon"); $("sim").classList.add("show"); $("more").classList.remove("show");
  $("bsim").style.display = "none"; $("bgo").textContent = "Start walking";
  placeRecenter(); render();
  toast("Simulation: tap Start walking");
}
function exitSim() {
  if (tracking) stopTracking();
  simMode = false; simDetour = null; simBad = false; $("sbad").classList.remove("on");
  s = Math.min(store.get("pos", 0), S.total);
  offCount = 0; lastOnRoute = 0; lastFix = null; alerted.clear(); resetBelief(s); me.remove();
  $("bar").classList.remove("simon"); $("sim").classList.remove("show");
  $("bsim").style.display = ""; $("bgo").textContent = s > 0 ? "Resume" : "Start";
  follow = true; placeRecenter(); render();
  toast("Back to your real progress");
}

// ---------- route
async function openRoute() {
  const r = await fetch("data/route.json");
  S = prepare(await r.json());
  s = Math.min(store.get("pos", 0), S.total);
  alerted.clear(); offCount = 0; lastOnRoute = 0; resetBelief(s);
  for (const l of ["ahead", "preview"]) lyr[l].setStyle({ color: S.c });
  lyr.ends.clearLayers();
  for (const [dd, nm] of S.stopD) {
    const p = at(dd);
    L.circleMarker([p.lat, p.lon], { radius: 6, color: "#fff", weight: 2, fillColor: "#111", fillOpacity: 1 })
      .bindTooltip(`Good place to stop · Metro ${nm}`).addTo(lyr.ends);
  }
  $("bgo").textContent = s > 0 ? "Resume" : "Start";
  follow = true; render();
}

// ---------- UI
function toast(t) { const e = $("toast"); e.textContent = t; e.style.display = "block"; clearTimeout(toast.t); toast.t = setTimeout(() => e.style.display = "none", 2500); }
function buzz(p) { try { navigator.vibrate?.(p); } catch {} }

$("bgo").onclick = () => { if (S) tracking ? stopTracking() : startTracking(); };
$("bmore").onclick = () => { if (simMode) $("sim").classList.toggle("show"); else $("more").classList.toggle("show"); placeRecenter(); };
$("bsim").onclick = enterSim;
$("sexit").onclick = exitSim;
$("swrong").onclick = () => {
  if (!simMode || !tracking) { toast("Start walking first"); return; }
  if (simDetour) return;
  const a = at(simS), b = at(simS + 5), dx = b.x - a.x, dy = b.y - a.y, L = Math.hypot(dx, dy) || 1;
  simDetour = { phase: "out", off: 0, nx: -dy / L, ny: dx / L };     // leave to the left
  toast("Walking off the route…");
};
$("sbad").onclick = () => { simBad = !simBad; $("sbad").classList.toggle("on", simBad); toast(simBad ? "Bad GPS on" : "Bad GPS off"); };
$("srelocate").onclick = relocate;
function placeRecenter() { $("recenter").style.bottom = ($("bar").getBoundingClientRect().height + 22) + "px"; }
window.addEventListener("resize", placeRecenter); placeRecenter();
$("sim").querySelectorAll("[data-x]").forEach(b => b.onclick = () => {
  simMult = +b.dataset.x;
  $("sim").querySelectorAll("[data-x]").forEach(o => o.classList.toggle("on", o === b));
});
$("relocate").onclick = relocate;
$("recenter").onclick = () => { follow = true; render(); };
map.on("dragstart", () => { follow = false; });

(async () => {
  await openRoute();
  if ("serviceWorker" in navigator && window.isSecureContext) navigator.serviceWorker.register("sw.js").catch(() => {});
})();
