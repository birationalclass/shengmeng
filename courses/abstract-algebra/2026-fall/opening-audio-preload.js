/* Download each score in full before the opening offers to begin. */
(() => {
  'use strict';
  function create(audio, source) {
    let pending = null, complete = false, objectUrl = null, progress = 0;
    const listeners = new Set();
    const notify = value => { progress = value; for (const report of listeners) report(value); };
    function prepare(report = () => {}) {
      if (complete && audio.readyState >= 2 && !audio.error) { report(1); return Promise.resolve(); }
      // Web views may evict decoded media while the course is in the foreground.
      if(complete){complete=false;progress=0;}
      listeners.add(report); report(progress);
      if (pending) return pending;
      pending = (async () => {
        const abort = new AbortController();
        let watchdog = 0;
        const touch = () => { clearTimeout(watchdog); watchdog = setTimeout(() => abort.abort(), 45000); };
        try {
          notify(0); touch();
          const response = await fetch(objectUrl || source, {signal: abort.signal});
          if (!response.ok) throw new Error('Music download failed');
          const total = Number(response.headers.get('Content-Length')) || 0;
          let blob;
          if (response.body?.getReader) {
            const reader = response.body.getReader(), chunks = [];
            let received = 0;
            while (true) {
              const {done, value} = await reader.read();
              if (done) break;
              chunks.push(value); received += value.byteLength; touch();
              if (total > 0) notify(.96 * Math.min(1, received / total));
            }
            blob = new Blob(chunks, {type: 'audio/mpeg'});
          } else blob = await response.blob();
          if (!blob.size) throw new Error('Empty music download');
          clearTimeout(watchdog); notify(.96);
          if(objectUrl)URL.revokeObjectURL(objectUrl);
          objectUrl = URL.createObjectURL(blob);
          await new Promise((resolve, reject) => {
            const cleanup = () => { clearTimeout(watchdog); audio.removeEventListener('loadeddata', ready); audio.removeEventListener('error', failed); };
            const ready = () => { if (audio.readyState >= 2) { cleanup(); resolve(); } };
            const failed = () => { cleanup(); reject(new Error('Music could not be prepared')); };
            audio.addEventListener('loadeddata', ready);
            audio.addEventListener('error', failed);
            watchdog = setTimeout(failed, 20000);
            audio.preload = 'auto'; audio.src = objectUrl; audio.load(); ready();
          });
          complete = true; notify(1);
        } catch (error) {
          if (objectUrl) { audio.removeAttribute('src'); audio.load(); URL.revokeObjectURL(objectUrl); objectUrl = null; }
          throw error;
        } finally { clearTimeout(watchdog); }
      })().finally(() => { pending = null; listeners.clear(); });
      return pending;
    }
    return {prepare};
  }
  window.CourseOpeningAudioPreload = {create};
})();
