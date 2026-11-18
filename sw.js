// Offline support: app files and stage data are cached when first loaded,
// map tiles are cached as you view them (open a stage's area once on wifi).
const APP = "pw-app-v1", TILES = "pw-tiles-v1";
const SHELL = ["./", "index.html", "app.js", "manifest.webmanifest", "icon.svg", "data/index.json",
  "https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.min.css",
  "https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.min.js"];

self.addEventListener("install", e => e.waitUntil(caches.open(APP).then(c => c.addAll(SHELL)).then(() => self.skipWaiting())));
self.addEventListener("activate", e => e.waitUntil(self.clients.claim()));

self.addEventListener("fetch", e => {
  const url = new URL(e.request.url);
  if (e.request.method !== "GET") return;
  const isTile = url.hostname.endsWith("tile.openstreetmap.org");
  const cacheName = isTile ? TILES : APP;
  // network first for app files (so updates arrive), cache first for tiles
  e.respondWith(isTile
    ? caches.match(e.request).then(hit => hit || fetch(e.request).then(r => {
        const copy = r.clone(); caches.open(cacheName).then(c => c.put(e.request, copy)); return r; }))
    : fetch(e.request).then(r => {
        if (r.ok) { const copy = r.clone(); caches.open(cacheName).then(c => c.put(e.request, copy)); }
        return r; }).catch(() => caches.match(e.request)));
});
