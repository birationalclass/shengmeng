import { cameraBasis, makeRenderer } from './renderer.js';

const presets = [
  { name: '浑水岩池', english: 'ROCK POOL', eye: [0, 5.7, -10.5], yaw: 0, pitch: -0.411, fov: 51,
    clarity: 31, wind: 66, altitude: 31, azimuth: 64, light: 29, caustics: false },
  { name: '清水与焦散', english: 'CLEAR WATER & CAUSTICS', eye: [-0.8, 8.6, -6.55], yaw: 0.09, pitch: -0.78, fov: 44,
    clarity: 100, wind: 47, altitude: 65, azimuth: 52, light: 30, caustics: true },
  { name: '波峰散射', english: 'CREST SCATTERING', eye: [-5.7, 3.6, -10.2], yaw: 0.47, pitch: -0.23, fov: 46,
    clarity: 86, wind: 32, altitude: 16, azimuth: 17, light: 32, caustics: false }
];

const byId = id => document.getElementById(id);
const canvas = byId('surface');
const scene = byId('scene');
const pauseButton = byId('pause');
const status = byId('status');
const gestureButton = byId('gesture');
const immersiveButton = byId('immersive');
const exitButton = byId('exit');
const settings = [...document.querySelectorAll('[data-setting]')];
const parameters = ['clarity', 'wind', 'altitude', 'azimuth', 'light'];
const toggles = ['boat', 'drifting', 'caustics'];
const controlState = { setting: 0, viewMode: 0, boat: true, drifting: true };
const state = { ...presets[0], eye: [...presets[0].eye], time: 0, boatTime: 0 };
const reduced = matchMedia('(prefers-reduced-motion: reduce)');
let paused = reduced.matches;
let render;
let lastFrame;
let frame = 0;
const keys = new Set();
const pointers = new Map();
let zoomDistance = 0;
let lastHold = 0;
let lookMode = false;
let immersive = false;
const clamp = (value, low, high) => Math.min(high, Math.max(low, value));

function setStatus(message) {
  status.hidden = !message;
  status.textContent = message;
}

function sync() {
  const preset = presets[controlState.setting];
  byId('scene-en').textContent = preset.english;
  byId('scene-name').textContent = preset.name;
  for (const button of settings) button.setAttribute('aria-pressed', Number(button.dataset.setting) === controlState.setting);
  for (const parameter of parameters) {
    const input = byId(parameter);
    input.value = state[parameter];
    let value = String(state[parameter]);
    if (parameter === 'light') value = (state.light / 10).toFixed(1);
    if (parameter === 'clarity' || parameter === 'wind') value += '%';
    if (parameter === 'altitude' || parameter === 'azimuth') value = value.replace('-', '−') + '°';
    byId(parameter + '-value').textContent = value;
    input.setAttribute('aria-valuetext', value);
  }
  for (const key of toggles) {
    const input = byId(key);
    input.checked = key === 'caustics' ? state.caustics : controlState[key];
    input.disabled = controlState.setting === 2 || (key === 'drifting' && !controlState.boat);
  }
  byId('view').value = controlState.viewMode;
  gestureButton.hidden = controlState.setting === 2;
  pauseButton.setAttribute('aria-pressed', paused);
  pauseButton.textContent = paused ? '继续' : '暂停';
  byId('touch-hint').textContent = controlState.setting === 2
    ? '滑动转动视角 · 双指缩放'
    : '滑动水面可激起涟漪 · 双指缩放';
  byId('desktop-hint').textContent = controlState.setting === 2
    ? '拖动转向 · WASD 移动 · Q / E 升降'
    : '左键划水 · 右键转向 · WASD 移动 · Q / E 升降';
}

function resetView() {
  const { eye, yaw, pitch, fov } = presets[controlState.setting];
  Object.assign(state, { eye: [...eye], yaw, pitch, fov });
  queue();
}

function choose(setting) {
  const preset = presets[setting];
  Object.assign(controlState, { setting, viewMode: 0, boat: true, drifting: true });
  Object.assign(state, preset, { eye: [...preset.eye], time: 0, boatTime: 0 });
  render?.resetRipples();
  sync();
  queue();
}

function move(dt) {
  if (!keys.size) return;
  const step = dt * (keys.has('Shift') ? 10 : 3.8);
  const { forward, right } = cameraBasis(state.yaw, 0);
  const forwardStep = Number(keys.has('w')) - Number(keys.has('s'));
  const sideStep = Number(keys.has('d')) - Number(keys.has('a'));
  state.eye[0] = clamp(state.eye[0] + (forward[0] * forwardStep + right[0] * sideStep) * step, -19, 19);
  state.eye[2] = clamp(state.eye[2] + (forward[2] * forwardStep + right[2] * sideStep) * step, -21, 20);
  state.eye[1] = clamp(state.eye[1] + (Number(keys.has('e')) - Number(keys.has('q'))) * step, 0.38, 24);
  state.yaw += (Number(keys.has('ArrowLeft')) - Number(keys.has('ArrowRight'))) * dt * 1.12;
  state.pitch = clamp(state.pitch + (Number(keys.has('ArrowUp')) - Number(keys.has('ArrowDown'))) * dt * 0.95, -1.47, 1.37);
}

function worldAtScreen(clientX, clientY) {
  const rect = canvas.getBoundingClientRect();
  const { forward, right, up } = cameraBasis(state.yaw, state.pitch);
  const k = Math.tan(state.fov * Math.PI / 360);
  const x = k * (2 * (clientX - rect.left) / rect.width - 1) * rect.width / rect.height;
  const y = k * (1 - 2 * (clientY - rect.top) / rect.height);
  const direction = forward.map((f, i) => f + right[i] * x + up[i] * y);
  if (direction[1] >= -0.015) return null;
  const t = -state.eye[1] / direction[1];
  const world = [state.eye[0] + direction[0] * t, state.eye[2] + direction[2] * t];
  return world.some(v => Math.abs(v) >= 23) ? null : world;
}

function ripple(x, y, strength = 1) {
  if (!render || controlState.setting === 2) return;
  const at = worldAtScreen(x, y);
  if (!at) return;
  if (paused) {
    paused = false;
    sync();
  }
  render.disturb(...at, strength, 0.60);
  queue();
}

function animate(now) {
  frame = 0;
  if (!render || document.hidden) return;
  const elapsed = lastFrame === undefined ? 1 / 60 : (now - lastFrame) / 1000;
  const dt = Math.min(0.065, elapsed);
  lastFrame = now;
  move(dt);
  if (!paused) {
    state.time += dt;
    if (controlState.drifting && controlState.boat) state.boatTime += dt;
    const held = pointers.size === 1 ? pointers.values().next().value : undefined;
    if (held && !held.turn && now - lastHold > 85 && now - held.fired > 78) {
      ripple(held.x, held.y, 0.19);
      lastHold = now;
    }
  }
  render.draw({
    ...state, ...controlState,
    clarity: state.clarity / 100, wind: state.wind / 100, light: state.light / 10,
    roughness: 0.18 + 0.075 * state.wind / 100
  }, paused ? 0 : dt);
  if (!paused || keys.size) queue();
}

function queue() {
  if (!frame && render && !document.hidden) frame = requestAnimationFrame(animate);
}

function init() {
  try {
    render = makeRenderer(canvas);
    render.draw({ ...state, ...controlState, clarity: state.clarity / 100, wind: state.wind / 100,
      light: state.light / 10, roughness: 0.23 }, 0);
    setStatus('');
    queue();
  } catch (error) {
    render = undefined;
    console.error('水体试验1116渲染出错', error);
    setStatus('当前浏览器无法启动 WebGL 2 水体渲染。');
  }
}

for (const button of settings) button.addEventListener('click', () => choose(Number(button.dataset.setting)));
for (const parameter of parameters) byId(parameter).addEventListener('input', event => {
  state[parameter] = Number(event.currentTarget.value);
  sync();
  queue();
});
for (const key of toggles) byId(key).addEventListener('change', event => {
  if (key === 'caustics') state.caustics = event.currentTarget.checked;
  else controlState[key] = event.currentTarget.checked;
  sync();
  queue();
});
byId('view').addEventListener('change', event => {
  controlState.viewMode = Number(event.currentTarget.value);
  queue();
});
byId('reset-view').addEventListener('click', resetView);
byId('reset').addEventListener('click', () => choose(controlState.setting));
pauseButton.addEventListener('click', () => {
  paused = !paused;
  lastFrame = undefined;
  sync();
  queue();
});
gestureButton.addEventListener('click', () => {
  lookMode = !lookMode;
  gestureButton.textContent = lookMode ? '划动水面' : '转动视角';
  gestureButton.setAttribute('aria-pressed', lookMode);
  canvas.dataset.look = lookMode;
});

const moveKeys = new Set(['w','a','s','d','q','e','Shift','ArrowLeft','ArrowRight','ArrowUp','ArrowDown']);
canvas.addEventListener('keydown', event => {
  const key = event.key.length === 1 ? event.key.toLowerCase() : event.key;
  if (!moveKeys.has(key)) return;
  event.preventDefault();
  if (keys.size === 0 && paused) lastFrame = undefined;
  keys.add(key);
  queue();
});
window.addEventListener('keyup', event => keys.delete(event.key.length === 1 ? event.key.toLowerCase() : event.key));
canvas.addEventListener('blur', () => keys.clear());
window.addEventListener('blur', () => keys.clear());

canvas.addEventListener('contextmenu', event => event.preventDefault());
canvas.addEventListener('pointerdown', event => {
  if (event.button > 2) return;
  const turn = event.button === 2 || event.shiftKey || lookMode || controlState.setting === 2;
  const point = { x: event.clientX, y: event.clientY, fired: event.timeStamp, turn };
  canvas.focus({ preventScroll: true });
  canvas.setPointerCapture(event.pointerId);
  pointers.set(event.pointerId, point);
  if (pointers.size === 1 && !turn) ripple(point.x, point.y);
});
canvas.addEventListener('pointermove', event => {
  const point = pointers.get(event.pointerId);
  if (!point) return;
  const dx = event.clientX - point.x;
  const dy = event.clientY - point.y;
  point.x = event.clientX;
  point.y = event.clientY;
  if (pointers.size === 2) {
    const [a, b] = pointers.values();
    const distance = Math.hypot(b.x - a.x, b.y - a.y);
    if (zoomDistance > 5) state.fov = clamp(state.fov * zoomDistance / distance, 30, 77);
    zoomDistance = distance;
  } else if (point.turn) {
    state.yaw -= dx * 0.0045;
    state.pitch = clamp(state.pitch + dy * 0.0045, -1.47, 1.37);
  } else if (event.timeStamp - point.fired >= 38) {
    ripple(point.x, point.y, clamp(Math.hypot(dx, dy) / 15, 0.22, 0.90));
    point.fired = event.timeStamp;
  }
  queue();
});
function removePointer(event) {
  pointers.delete(event.pointerId);
  zoomDistance = 0;
}
canvas.addEventListener('pointerup', removePointer);
canvas.addEventListener('pointercancel', removePointer);
canvas.addEventListener('lostpointercapture', removePointer);
canvas.addEventListener('wheel', event => {
  event.preventDefault();
  state.fov = clamp(state.fov + event.deltaY * 0.036, 30, 77);
  queue();
}, { passive: false });

function setImmersive(enabled) {
  immersive = enabled;
  scene.classList.toggle('immersive', enabled);
  immersiveButton.setAttribute('aria-pressed', enabled);
  exitButton.hidden = !enabled;
  byId('workbench').inert = enabled;
  document.querySelector('.masthead').inert = enabled;
  document.querySelector('.credits').inert = enabled;
  document.body.style.overflow = enabled ? 'hidden' : '';
  (enabled ? exitButton : immersiveButton).focus({ preventScroll: true });
  queue();
}
immersiveButton.addEventListener('click', () => setImmersive(true));
exitButton.addEventListener('click', () => setImmersive(false));
document.addEventListener('keydown', event => {
  if (event.key === 'Escape' && immersive) setImmersive(false);
});
canvas.addEventListener('webglcontextlost', event => {
  event.preventDefault();
  render = undefined;
  setStatus('渲染已中断，正在恢复…');
});
canvas.addEventListener('webglcontextrestored', init);
document.addEventListener('visibilitychange', () => {
  lastFrame = undefined;
  queue();
});
new ResizeObserver(queue).observe(scene);
sync();
init();
