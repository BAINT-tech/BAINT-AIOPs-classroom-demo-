/* BAINT AI service worker: lets the app open with no data after the first visit,
   and lets notifications work on Android (which needs a service worker). */
const CACHE = "baint-v39-2";
const SHELL = ["./", "lessons.js", "solver.js", "logo.png"];

self.addEventListener("install", event => {
  event.waitUntil(
    caches.open(CACHE)
      .then(cache => Promise.all(SHELL.map(url => cache.add(url).catch(() => null))))
      .then(() => self.skipWaiting())
  );
});

self.addEventListener("activate", event => {
  event.waitUntil(
    caches.keys()
      .then(keys => Promise.all(keys.filter(k => k !== CACHE).map(k => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

/* Show the saved copy instantly (works offline), and refresh it in the background when online. */
self.addEventListener("fetch", event => {
  const req = event.request;
  if(req.method !== "GET" || new URL(req.url).origin !== self.location.origin) return;
  event.respondWith(
    caches.open(CACHE).then(cache =>
      cache.match(req, {ignoreSearch: true}).then(saved => {
        const fresh = fetch(req).then(res => {
          if(res && res.ok) cache.put(req, res.clone());
          return res;
        }).catch(() => saved);
        return saved || fresh;
      })
    )
  );
});

self.addEventListener("notificationclick", event => {
  event.notification.close();
  event.waitUntil(
    self.clients.matchAll({type: "window", includeUncontrolled: true}).then(list => {
      if(list.length) return list[0].focus();
      return self.clients.openWindow("./");
    })
  );
});
