(() => {
  'use strict';

  // The opening's music manager remains the authority for user consent and UI.
  // This adapter changes gains without changing the original track or its loop.
  function create({ mainAudio, trackUrl = './audio/the-great-eagle.mp3', requestMain } = {}) {
    if (!mainAudio) throw new TypeError('A mainAudio element is required.');
    const score = new Audio(trackUrl);
    score.preload = 'auto';
    score.loop = false;
    score.volume = 0;
    let state = { active: false, prelude: false, departing: false, t: 0, dt: 0, direction: 1, playing: false, enabled: true, volume: .72 };
    let authorized = false, blocked = false, failed = false, destroyed = false;
    let mix = 0, fade = null, mainGain = 1, mainFade = null, entryFading = false, clock = 0, lastSeekAt = -Infinity, needSync = true;
    let playEpoch = 0, scoreRequest = null, mainRequested = false, readySettled = false;
    let readyResolve;
    const ready = new Promise(resolve => { readyResolve = resolve; });
    const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));
    const finite = (v, fallback) => Number.isFinite(Number(v)) ? Number(v) : fallback;
    const visible = () => typeof document === 'undefined' || !document.hidden;
    const allowed = () => authorized && !destroyed && state.playing && state.enabled && visible();
    const wantsScore = () => allowed() && !state.prelude && !state.departing && state.active && state.direction >= 0 && !failed && !blocked;
    const reverse = () => state.active && state.direction < 0;
    const duration = () => Number.isFinite(score.duration) && score.duration > 0 ? score.duration : null;
    const atEnd = () => duration() !== null && state.t >= duration() - .025;

    function settleReady() {
      if (readySettled) return;
      readySettled = true;
      readyResolve({ ready: !failed, duration: duration(), failed });
    }

    function pauseScore() {
      playEpoch++;
      scoreRequest = null;
      score.pause();
    }

    function seekScore(force = false) {
      if (score.seeking || (!force && clock - lastSeekAt < 700)) return;
      const target = clamp(state.t, 0, duration() === null ? Infinity : Math.max(0, duration() - .002));
      if (!force && Math.abs(score.currentTime - target) <= .35) return;
      // A server without byte ranges can report seekable [0, 0] even when a
      // large part is buffered. Seeking then silently jumps to zero in Chrome.
      if (score.seekable && score.readyState > 0 && target > .05) {
        let available = false;
        for (let i = 0; i < score.seekable.length; i++) {
          if (target >= score.seekable.start(i) - .05 && target <= score.seekable.end(i) + .05) available = true;
        }
        if (!available) { needSync = true; return; }
      }
      try {
        score.currentTime = target;
        lastSeekAt = clock;
        needSync = false;
      } catch (_) { needSync = true; }
    }

    function ensureMain() {
      if (!allowed() || reverse() || status().suppressMain || mainRequested || !mainAudio.paused) return;
      mainRequested = true;
      try {
        const result = requestMain ? requestMain() : mainAudio.play();
        if (result && typeof result.then === 'function') {
          result.then(() => {
            if (!allowed() || reverse() || status().suppressMain) mainAudio.pause();
          }).catch(() => {});
        }
      } catch (_) { /* The master music manager reports its own playback errors. */ }
    }

    function scoreFailed() {
      failed = true;
      blocked = false;
      pauseScore();
      mix = 0;
      fade = null;
      mainRequested = false;
      settleReady();
      applyVolumes();
      ensureMain();
    }

    function requestScore(unlocking = false) {
      if (scoreRequest || failed || destroyed || !authorized) return scoreRequest || Promise.resolve(false);
      if (!unlocking && (!wantsScore() || atEnd())) return Promise.resolve(false);
      if (wantsScore()) seekScore(needSync);
      const epoch = ++playEpoch;
      let promise;
      try { promise = score.play(); }
      catch (error) { promise = Promise.reject(error); }
      scoreRequest = Promise.resolve(promise).then(() => {
        if (epoch !== playEpoch) {
          if (!wantsScore() || atEnd()) score.pause();
          return false;
        }
        scoreRequest = null;
        blocked = false;
        if (!wantsScore() || atEnd()) {
          score.pause();
          if (unlocking && !state.active) { try { score.currentTime = 0; } catch (_) {} }
        }
        return !score.paused;
      }).catch(error => {
        if (epoch !== playEpoch) return false;
        scoreRequest = null;
        if (error && error.name === 'NotAllowedError') {
          blocked = true;
          mainRequested = false;
          ensureMain();
        } else if (!error || error.name !== 'AbortError') scoreFailed();
        return false;
      });
      return scoreRequest;
    }

    function applyVolumes() {
      if (!allowed()) {
        mainAudio.volume = 0;
        score.volume = 0;
        return;
      }
      const angle = mix * Math.PI / 2;
      mainAudio.volume = state.volume * Math.cos(angle) * mainGain;
      score.volume = state.volume * Math.sin(angle);
    }

    function advanceFade(target, dt) {
      if (!fade || fade.target !== target) {
        fade = { from: mix, target, elapsed: 0 };
      }
      fade.elapsed = Math.min(3000, fade.elapsed + dt);
      const u = fade.elapsed / 3000;
      const ease = u * u * u * (10 + u * (-15 + 6 * u));
      mix = fade.from + (fade.target - fade.from) * ease;
      if (fade.elapsed === 3000) mix = target;
    }

    function advanceMainGain(dt) {
      const target = state.departing || state.prelude || entryFading && state.active && !failed && !blocked ? 0 : 1;
      if (!mainFade || mainFade.target !== target) mainFade = { from: mainGain, target, elapsed: 0 };
      mainFade.elapsed = Math.min(3000, mainFade.elapsed + dt);
      const u = mainFade.elapsed / 3000, ease = u * u * u * (10 + u * (-15 + 6 * u));
      mainGain = mainFade.from + (target - mainFade.from) * ease;
      if (mainFade.elapsed === 3000) mainGain = target;
    }

    function update(next = {}) {
      if (destroyed) return status();
      const previous = state;
      state = {
        active: next.active === undefined ? previous.active : Boolean(next.active),
        prelude: next.prelude === undefined ? previous.prelude : Boolean(next.prelude),
        departing: next.departing === undefined ? previous.departing : Boolean(next.departing),
        t: Math.max(0, finite(next.t, previous.t)),
        dt: clamp(finite(next.dt, 0), 0, 250),
        direction: finite(next.direction, previous.direction),
        playing: next.playing === undefined ? previous.playing : Boolean(next.playing),
        enabled: next.enabled === undefined ? previous.enabled : Boolean(next.enabled),
        volume: clamp(finite(next.volume, previous.volume), 0, 1)
      };
      clock += state.dt;
      if (state.prelude) entryFading = true;
      if (!state.prelude && !state.active) entryFading = false;
      // Start the original track's fade with the visual entry. Its silent hold
      // remains in place while the portrait forms and the new score prepares.
      if (state.playing && visible()) advanceMainGain(state.dt);
      const resumed = !previous.playing && state.playing || !previous.enabled && state.enabled;
      const changedDirection = previous.direction < 0 && state.direction >= 0;
      if (previous.active !== state.active || resumed || changedDirection) {
        needSync = true;
        mainRequested = false;
      }
      if (!allowed()) {
        if (!score.paused || scoreRequest) pauseScore();
        mainAudio.pause();
        applyVolumes();
        return status();
      }
      if (reverse()) {
        if (!score.paused || scoreRequest) pauseScore();
        mainAudio.pause();
        mainAudio.volume = 0;
        score.volume = 0;
        needSync = true;
        return status();
      }

      if (wantsScore() && !atEnd()) {
        if (score.paused) requestScore();
        else seekScore(needSync);
      } else if (state.active && (!score.paused || scoreRequest)) {
        pauseScore();
      }
      // Ordinary crossfades retain the main track during buffering; an explicit
      // entry fade keeps it silent while the portrait and score prepare.
      const scoreAudible = wantsScore() && !score.paused && score.readyState >= 2 && !atEnd();
      const target = scoreAudible ? 1 : 0;
      if (!target) ensureMain();
      advanceFade(target, state.dt);
      applyVolumes();
      if (mix >= 1 - 1e-7 && target || mainGain <= 1e-7) {
        mainAudio.pause();
        mainRequested = false;
      }
      if (mix <= 1e-7 && !target && !state.active && (!score.paused || scoreRequest)) pauseScore();
      return status();
    }

    function unlock() {
      if (destroyed) return Promise.resolve(false);
      if (authorized && !blocked && !failed) return scoreRequest || Promise.resolve(true);
      authorized = true;
      blocked = false;
      // This silent play must be called synchronously from the entry gesture.
      // It unlocks the second media element; playback stops until it is needed.
      score.volume = 0;
      return requestScore(true);
    }

    function stop(options = {}) {
      const reset = typeof options === 'boolean' ? options : options.reset !== false;
      authorized = false;
      state = { ...state, active: false, prelude: false, departing: false, playing: false };
      blocked = false;
      pauseScore();
      mainAudio.pause();
      mainAudio.volume = state.volume;
      score.volume = 0;
      mix = 0;
      fade = null;
      mainGain = 1;mainFade = null;entryFading = false;
      needSync = true;
      mainRequested = false;
      if (reset) { try { score.currentTime = 0; } catch (_) {} }
    }

    function status() {
      return {
        authorized, active: state.active, prelude: state.prelude, departing: state.departing, mainGain, blocked, failed,
        currentTime: finite(score.currentTime, 0), duration: duration(),
        scorePlaying: allowed() && !score.paused && score.volume > .001,
        scoreOwnsMusic: state.departing || state.prelude || state.active && !failed && !blocked || mix > .001,
        // A requested entry fade owns the music even during its quiet interval.
        suppressMain: state.departing || state.prelude || entryFading && state.active && !failed && !blocked || wantsScore() && !score.paused && score.readyState >= 2 && !atEnd() && mix >= 1 - 1e-7,
        mix, mainVolume: mainAudio.volume, scoreVolume: score.volume,
        paused: score.paused, seeking: score.seeking, needsSync: needSync, ready: score.readyState >= 2,
        direction: state.direction, ended: atEnd()
      };
    }

    function onMetadata() { settleReady(); }
    function onHidden() {
      if (visible()) return;
      pauseScore();
      mainAudio.pause();
      mainAudio.volume = 0;
      score.volume = 0;
      needSync = true;
      mainRequested = false;
    }
    score.addEventListener('loadedmetadata', onMetadata);
    score.addEventListener('error', scoreFailed);
    if (typeof document !== 'undefined') document.addEventListener('visibilitychange', onHidden);
    return {
      start: unlock, unlock, update, stop, status, ready,
      get currentTime() { return finite(score.currentTime, 0); },
      destroy() {
        stop();
        destroyed = true;
        score.removeEventListener('loadedmetadata', onMetadata);
        score.removeEventListener('error', scoreFailed);
        if (typeof document !== 'undefined') document.removeEventListener('visibilitychange', onHidden);
        score.removeAttribute('src');
        score.load();
        settleReady();
      }
    };
  }

  window.CourseOpeningGaloisAudio = { create };
})();
