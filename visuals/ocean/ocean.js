import { OceanRenderer } from './ocean-renderer.js?v=20260925-ocean-5';
const $ = (id) => document.getElementById(id);
const canvas = $('ocean');
const state = { wave: 1.2, wind: .45, sun: 5, speed: 1, time: 7.1, paused: matchMedia('(prefers-reduced-motion: reduce)').matches, yaw: 0, pitch: 0, distance: 0, quality: 'auto', scale: 1 };
const presets = {
  golden: { wave: 1.2, wind: 45, sun: 5, name: '落日熔金', english: 'THE GOLDEN HOUR', number: '01' },
  clear: { wave: 1.5, wind: 60, sun: 24, name: '晴日碧海', english: 'A BREATH OF BLUE', number: '02' },
  blue: { wave: .8, wind: 30, sun: -2, name: '暮色将至', english: 'AFTER THE SUN', number: '03' }
};
let gl, program, oceanRenderer, raf = 0, last = 0, frames = 0, sampleStart = 0, slowSamples = 0, frameInterval = 0, lastRendered = 0;
let dragging = false, pointerId = null, pointerX = 0, pointerY = 0;
let toastTimer, audioContext, audioGain, audioSource, soundOn = false, downloadRequested = false;
const audioSupported = Boolean(window.AudioContext || window.webkitAudioContext);

function message(text) {
  $('message').textContent = text;
  $('message').classList.add('visible');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => $('message').classList.remove('visible'), 3000);
}
function updateInput(id) {
  const input = $(id), value = Number(input.value);
  state[id] = id === 'wind' ? value / 100 : value;
  $(id + 'Value').textContent = id === 'wave' ? `${value.toFixed(1)} m` : id === 'wind' ? `${value}%` : id === 'sun' ? `${value}°` : `${value.toFixed(1)}×`;
  input.style.setProperty('--fill', `${100 * (value - Number(input.min)) / (Number(input.max) - Number(input.min))}%`);
  renderOnce();
}
function resize() {
  const rect = canvas.getBoundingClientRect();
  const maxPixels = state.quality === 'high' ? 2500000 : state.quality === 'low' ? 650000 : 1450000 * state.scale;
  const ratio = Math.min(devicePixelRatio || 1, Math.sqrt(maxPixels / (rect.width * rect.height)));
  const w = Math.max(1, Math.round(rect.width * ratio)), h = Math.max(1, Math.round(rect.height * ratio));
  if (canvas.width !== w || canvas.height !== h) { canvas.width = w; canvas.height = h; }
  if (oceanRenderer) oceanRenderer.resize(w, h);
  renderOnce();
}
async function init() {
  oceanRenderer = new OceanRenderer(canvas);
  gl = oceanRenderer.renderer.getContext();
  program = true;
  resize();
  syncPlayButton();
  $('renderStatus').textContent = state.paused ? '已暂停 · 随时继续' : '实时生成 · 随风而动';
  sampleStart = performance.now();
  schedule();
}
function draw() {
  if (!program || gl.isContextLost()) return;
  oceanRenderer.draw(state);
  canvas.dataset.time = state.time.toFixed(3);
  if (downloadRequested) {
    downloadRequested = false;
    canvas.toBlob(blob => {
      if (!blob) { message('图片保存失败，请重试'); return; }
      const url = URL.createObjectURL(blob), a = document.createElement('a');
      a.download = `between-tides-${new Date().toISOString().slice(0, 10)}.png`; a.href = url; document.body.append(a); a.click(); a.remove();
      setTimeout(() => URL.revokeObjectURL(url), 10000);
      message('已保存这片海');
    }, 'image/png');
  }
}
function schedule() { if (!raf && !document.hidden && !state.paused && program) raf = requestAnimationFrame(frame); }
function renderOnce() { if (program) draw(); }
function frame(now) {
  raf = 0;
  if (document.hidden || state.paused || gl.isContextLost()) { last = 0; return; }
  if (last) state.time += Math.min((now - last) / 1000, .1) * state.speed;
  last = now;
  if (now - lastRendered >= frameInterval) {
    draw(); lastRendered = now; frames++;
    updateAudio();
    if (now - sampleStart > 2400) {
      const fps = frames * 1000 / (now - sampleStart);
      canvas.dataset.fps = fps.toFixed(1);
      if (state.quality === 'auto' && fps < 27 && state.scale > .30) {
        slowSamples++;
        if (slowSamples >= 2) { state.scale *= .76; resize(); slowSamples = 0; }
      }
      frames = 0; sampleStart = now;
      $('renderStatus').textContent = '实时生成 · 随风而动';
    }
  }
  schedule();
}
function syncPlayButton() {
  $('playButton').setAttribute('aria-pressed', String(state.paused));
  $('playButton').setAttribute('aria-label', state.paused ? '继续海浪' : '暂停海浪');
  $('playIcon').textContent = state.paused ? '▷' : 'Ⅱ';
  $('stepButton').hidden = !state.paused;
  $('renderStatus').textContent = state.paused ? '已暂停 · 随时继续' : '实时生成 · 随风而动';
}
function togglePlay() {
  state.paused = !state.paused; last = 0;
  syncPlayButton();
  if (state.paused) { cancelAnimationFrame(raf); raf = 0; } else { sampleStart = performance.now(); frames = 0; schedule(); }
  updateAudio();
}
function hideInterface(hidden) {
  document.body.classList.toggle('ui-hidden', hidden);
  document.querySelectorAll('.interface').forEach(element => { element.inert = hidden; });
  $('showUI').hidden = !hidden;
  if (hidden) $('showUI').focus({ preventScroll: true }); else $('hideButton').focus({ preventScroll: true });
}
async function fullscreen() {
  try {
    if (document.fullscreenElement) await document.exitFullscreen();
    else if (document.documentElement.requestFullscreen) await document.documentElement.requestFullscreen();
    else message('当前浏览器不支持全屏，可隐藏界面欣赏海面');
  } catch { message('全屏暂不可用，可隐藏界面欣赏海面'); }
}
async function toggleSound() {
  try {
    if (!audioContext) {
      audioContext = new (window.AudioContext || window.webkitAudioContext)();
      const buffer = audioContext.createBuffer(1, audioContext.sampleRate * 12, audioContext.sampleRate);
      const channel = buffer.getChannelData(0);
      let brown = 0;
      for (let i = 0; i < channel.length; i++) { brown = (brown + Math.random() * .04 - .02) / 1.02; channel[i] = brown * 3.5; }
      audioSource = audioContext.createBufferSource(); audioSource.buffer = buffer; audioSource.loop = true;
      const filter = audioContext.createBiquadFilter(); filter.type = 'lowpass'; filter.frequency.value = 1250;
      audioGain = audioContext.createGain(); audioGain.gain.value = 0;
      audioSource.connect(filter).connect(audioGain).connect(audioContext.destination); audioSource.start();
    }
    await audioContext.resume(); soundOn = !soundOn;
    $('soundButton').setAttribute('aria-pressed', String(soundOn));
    $('soundButton').setAttribute('aria-label', soundOn ? '关闭海浪声' : '开启海浪声');
    updateAudio();
  } catch { message('此浏览器暂不能播放海浪声'); }
}
function updateAudio() {
  if (audioGain) {
    const volume = soundOn && !document.hidden && !state.paused ? .22 + .15 * Math.sin(state.time * .88) : 0;
    audioGain.gain.setTargetAtTime(volume, audioContext.currentTime, .3);
  }
}
for (const id of ['wave','wind','sun','speed']) {
  updateInput(id);
  $(id).addEventListener('input', () => updateInput(id));
}
document.querySelectorAll('[data-preset]').forEach(button => button.addEventListener('click', () => {
  const preset = presets[button.dataset.preset];
  document.querySelectorAll('[data-preset]').forEach(b => b.setAttribute('aria-pressed', String(b === button)));
  for (const id of ['wave','wind','sun']) { $(id).value = preset[id]; updateInput(id); }
  $('sceneName').textContent = preset.name; $('sceneEnglish').textContent = preset.english; $('sceneNumber').textContent = preset.number;
}));
$('playButton').addEventListener('click', togglePlay);
$('stepButton').addEventListener('click', () => { state.time += .5; renderOnce(); });
$('soundButton').addEventListener('click', toggleSound);
if (!audioSupported) { $('soundButton').disabled = true; $('soundButton').title = '当前浏览器不支持音频'; }
$('fullscreenButton').addEventListener('click', fullscreen);
document.addEventListener('fullscreenchange', () => $('fullscreenButton').setAttribute('aria-label', document.fullscreenElement ? '退出全屏' : '进入全屏'));
$('captureButton').addEventListener('click', () => { downloadRequested = true; renderOnce(); });
$('hideButton').addEventListener('click', () => hideInterface(true));
$('showUI').addEventListener('click', () => hideInterface(false));
$('resetButton').addEventListener('click', () => { state.yaw = state.pitch = state.distance = 0; renderOnce(); message('已回到海岸'); });
$('quality').addEventListener('change', event => { state.quality = event.target.value; state.scale = 1; frameInterval = state.quality === 'low' ? 30 : 0; resize(); });
$('aboutButton').addEventListener('click', () => $('aboutDialog').showModal());
$('closeAbout').addEventListener('click', () => $('aboutDialog').close());
$('aboutDialog').addEventListener('click', event => { if (event.target === $('aboutDialog')) { const r = event.target.getBoundingClientRect(); if (event.clientX < r.left || event.clientX > r.right || event.clientY < r.top || event.clientY > r.bottom) event.target.close(); } });
canvas.addEventListener('pointerdown', event => { if (event.button !== 0) return; dragging = true; pointerId = event.pointerId; pointerX = event.clientX; pointerY = event.clientY; canvas.setPointerCapture(pointerId); });
canvas.addEventListener('pointermove', event => {
  if (!dragging || event.pointerId !== pointerId) return;
  state.yaw = Math.max(-.65, Math.min(.65, state.yaw - (event.clientX - pointerX) * .0018));
  state.pitch = Math.max(-.12, Math.min(.22, state.pitch + (event.clientY - pointerY) * .0011));
  pointerX = event.clientX; pointerY = event.clientY; renderOnce();
});
for (const type of ['pointerup','pointercancel','lostpointercapture']) canvas.addEventListener(type, () => { dragging = false; pointerId = null; });
canvas.addEventListener('wheel', event => { event.preventDefault(); state.distance = Math.max(-1.2, Math.min(5., state.distance + event.deltaY * .005)); renderOnce(); }, { passive: false });
document.addEventListener('keydown', event => {
  if (/INPUT|SELECT|TEXTAREA/.test(event.target.tagName) || $('aboutDialog').open || event.ctrlKey || event.metaKey || event.altKey) return;
  if (event.code === 'Space' && !/BUTTON|A/.test(event.target.tagName)) { event.preventDefault(); togglePlay(); }
  if (event.key.toLowerCase() === 'f') fullscreen();
  if (event.key.toLowerCase() === 'h') hideInterface(!document.body.classList.contains('ui-hidden'));
});
document.addEventListener('visibilitychange', () => { last = 0; frames = 0; sampleStart = performance.now(); if (document.hidden) { cancelAnimationFrame(raf); raf = 0; } else schedule(); updateAudio(); });
window.addEventListener('resize', resize);
canvas.addEventListener('webglcontextlost', event => { event.preventDefault(); cancelAnimationFrame(raf); raf = 0; message('图形连接中断，正在等待恢复'); });
canvas.addEventListener('webglcontextrestored', () => { program = null; init().catch(fail); });
function fail(error) { console.error('Ocean renderer:', error); $('fallback').hidden = false; document.body.classList.add('render-failed'); $('renderStatus').textContent = '海面未能加载'; }
init().catch(fail);
