(() => {
  'use strict';
  const dialog = document.getElementById('courseOpening');
  const audio = document.getElementById('openingMusic');
  const button = document.getElementById('openingMusicToggle');
  // A shared note silhouette for sound-on and sound-off, with a clear diagonal slash.
  button.innerHTML='<svg class="opening-music-symbol" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><g class="music-notes"><path d="M9 17.5V5.5l11-2v12M9 8.5l11-2"/><ellipse cx="6" cy="17.5" rx="3" ry="2.5"/><ellipse cx="17" cy="15.5" rx="3" ry="2.5"/></g><path class="music-mute-slash" d="M3 3l18 18"/></svg>';
  const key = 'courseOpeningMusic.v1';
  let enabled = true, active = false, blocked = false, failed = false, generation = 0;
  try { enabled = localStorage.getItem(key) !== 'off'; } catch (_) {}
  audio.volume = .72;
  const score=window.CourseOpeningGaloisAudio.create({mainAudio:audio,trackUrl:new URL('./audio/the-great-eagle.mp3',document.baseURI).href,requestMain:()=>play()});
  const mainPreparation=window.CourseOpeningAudioPreload.create(audio,audio.src);
  let lastFrame={active:false,prelude:false,departing:false,t:0,dt:0,direction:1};
  function wanted() { return active && dialog.open && !document.hidden && enabled && !failed; }
  function sync() {
    const track=score.status(),playing = wanted() && (!audio.paused||track.scorePlaying||track.scoreOwnsMusic);
    button.dataset.sound=playing?'on':'off';
    button.setAttribute('aria-label', failed ? '音乐暂不可用' : playing ? '关闭入场音乐' : '开启入场音乐');
    button.setAttribute('aria-pressed', String(playing));
    button.title=failed?'音乐暂不可用':playing?'关闭背景音乐':'开启背景音乐';
    button.disabled = failed;
    button.classList.toggle('needs-gesture', blocked && enabled);
    dialog.dataset.music = failed ? 'unavailable' : playing ? 'playing' : blocked && enabled ? 'awaiting-gesture' : 'paused';
  }
  function play() {
    if (!wanted()||score.status().suppressMain) { sync(); return; }
    const request = ++generation;
    // Keep this call synchronous with a replay click or activation gesture.
    audio.play().then(() => {
      if (!wanted()||score.status().suppressMain) audio.pause();
      if (request === generation) { blocked = false; sync(); }
    }).catch(error => {
      if (request !== generation || !wanted()) return;
      if (error.name === 'NotAllowedError') blocked = true;
      else if (error.name !== 'AbortError') failed = true;
      sync();
    });
  }
  function stop(reset = true) {
    active = false; generation++; blocked = false; score.stop({reset}); audio.pause();
    if (reset) { try { audio.currentTime = 0; } catch (_) {} }
    sync();
  }
  button.addEventListener('click', () => {
    if (failed) return;
    if (!enabled || blocked) { enabled = true; blocked = false; score.unlock(); }
    else { enabled = false; generation++; audio.pause(); }
    try { localStorage.setItem(key, enabled ? 'on' : 'off'); } catch (_) {}
    score.update({...lastFrame,playing:active,enabled,dt:0});
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
  // Fullscreen briefly closes/reopens the dialog to restore its top layer.
  // The queued close event must not stop music in that still-open animation.
  dialog.addEventListener('close', () => { if (!dialog.open) stop(); });
  document.addEventListener('visibilitychange', () => {
    if (document.hidden) { generation++; audio.pause(); sync(); }
    else if (active) play();
  });
  window.addEventListener('pagehide', () => stop());
  window.CourseOpeningAudio = {
    async prepare(report = () => {}) {
      const progress=[0,0];
      const update=(index,value)=>{progress[index]=value;report((progress[0]+progress[1])/2,progress[0]<1?'加载开场配乐':'加载伽罗瓦配乐');};
      await Promise.all([mainPreparation.prepare(value=>update(0,value)),score.prepare(value=>update(1,value))]);
      failed=false;sync();
    },
    start() { active = true; failed = Boolean(audio.error); score.unlock(); play(); },
    frame(frame){lastFrame={...frame};score.update({...frame,playing:active&&dialog.open&&!document.hidden,enabled,volume:.72});sync();},
    scoreStatus:()=>score.status(),
    stop
  };
  sync();
})();
