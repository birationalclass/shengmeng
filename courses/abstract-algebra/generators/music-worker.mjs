import {TRACK_URL,readMeta,offlineResponse} from './music-cache.mjs';
self.addEventListener('install',event=>event.waitUntil(self.skipWaiting()));
self.addEventListener('activate',event=>event.waitUntil(self.clients.claim()));
// Only this audio URL is intercepted. Pages, login and game assets remain network-managed.
self.addEventListener('fetch',event=>{
 const request=event.request,url=new URL(request.url);
 if(url.origin+url.pathname!==TRACK_URL||!['GET','HEAD'].includes(request.method)||url.searchParams.has('offline-download'))return;
 event.respondWith((async()=>{
  try{const meta=await readMeta();if(meta?.complete)return offlineResponse(request,meta);}catch{}
  return fetch(request);
 })());
});
