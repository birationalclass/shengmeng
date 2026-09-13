(() => {
  'use strict';
  const dialog = document.getElementById('courseOpening');
  const audio = document.getElementById('openingMusic');
  const button = document.getElementById('openingMusicToggle');
  const key = 'courseOpeningMusic.v1';
  let enabled = true, active = false, blocked = false, failed = false, generation = 0;
  try { enabled = localStorage.getItem(key) !== 'off'; } catch (_) {}
  audio.volume = .72;
  function wanted() { return active && dialog.open && !document.hidden && enabled && !failed; }
  function sync() {
    const playing = wanted() && !audio.paused;
    button.textContent = failed ? '音乐暂不可用' : blocked && enabled ? '开启音乐' : playing ? '音乐 · 开' : '音乐 · 关';
    button.setAttribute('aria-label', failed ? '音乐暂不可用' : playing ? '关闭入场音乐' : '开启入场音乐');
    button.setAttribute('aria-pressed', String(playing));
    button.disabled = failed;
    button.classList.toggle('needs-gesture', blocked && enabled);
    dialog.dataset.music = failed ? 'unavailable' : playing ? 'playing' : blocked && enabled ? 'awaiting-gesture' : 'paused';
  }
  function play() {
    if (!wanted()) { sync(); return; }
    const request = ++generation;
    // Keep this call synchronous with a replay click or activation gesture.
    audio.play().then(() => {
      if (!wanted()) audio.pause();
      if (request === generation) { blocked = false; sync(); }
    }).catch(error => {
      if (request !== generation || !wanted()) return;
      if (error.name === 'NotAllowedError') blocked = true;
      else if (error.name !== 'AbortError') failed = true;
      sync();
    });
  }
  function stop(reset = true) {
    active = false; generation++; blocked = false; audio.pause();
    if (reset) { try { audio.currentTime = 0; } catch (_) {} }
    sync();
  }
  button.addEventListener('click', () => {
    if (failed) return;
    if (audio.paused || !enabled) { enabled = true; blocked = false; }
    else { enabled = false; generation++; audio.pause(); }
    try { localStorage.setItem(key, enabled ? 'on' : 'off'); } catch (_) {}
    if (enabled) play(); else sync();
  });
  dialog.addEventListener('pointerdown', event => {
    if (!event.target.closest('#openingMusicToggle') && blocked && enabled) play();
  });
  dialog.addEventListener('keydown', event => {
    if (![' ', 'Escape', 'Tab'].includes(event.key) && blocked && enabled) play();
  });
  audio.addEventListener('playing', sync);
  audio.addEventListener('pause', sync);
  audio.addEventListener('error', () => { failed = true; sync(); });
  dialog.addEventListener('close', () => stop());
  document.addEventListener('visibilitychange', () => {
    if (document.hidden) { generation++; audio.pause(); sync(); }
    else if (active) play();
  });
  window.addEventListener('pagehide', () => stop());
  window.CourseOpeningAudio = {
    start() { active = true; failed = Boolean(audio.error); play(); },
    stop,
    setDucked(value){audio.volume=value?.18:.72;}
  };
  sync();
})();
