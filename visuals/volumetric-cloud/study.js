import { cameraBasis, createCloudRenderer } from './renderer.js';
import { weatherData } from './weather-data.js';
import { javaWeatherData } from './weather-java.js';

const byId = id => document.getElementById(id);
const canvas = byId('cloudscape');
const viewport = byId('viewport');
const panel = byId('panel');
const map = byId('locate');
const satellite = byId('satellite-image');
const weatherMap = byId('weather-map');
const pin = byId('map-pin');
const status = byId('status');
const pause = byId('pause');
const enter = byId('enter');
const exit = byId('exit');
const presetButtons = [...document.querySelectorAll('[data-view]')];
const mapTabs = [...document.querySelectorAll('[data-map]')];
const clamp = (x, low, high) => Math.max(low, Math.min(high, x));
const degrees = 180 / Math.PI;
const directionDegrees = radians => Math.round(((radians * degrees + 540) % 360) - 180);
const minAltitude = 0.018;
const altitudeRange = 15 - minAltitude;
const datasets = [javaWeatherData, weatherData];
const datasetInput = byId('dataset');
datasetInput.disabled = true;
let activeDataset = datasets[0];
let initial = activeDataset.start;
let datasetRequest = 0;

function makeViews(dataset) {
  const start = dataset.start;
  const initialAzimuth = directionDegrees(start.yaw + 1.0);
  const marineBands = dataset === javaWeatherData;
  return {
    sea: { label: '从海面看云', altitude: minAltitude, pitch: 0.135, fov: 55, solarAltitude: 32, solarAzimuth: initialAzimuth, exposure: 0.95, cloudRange: 50 },
    inside: { label: '穿过云层', altitude: marineBands ? 1.63 : 2.6, pitch: 0.06, fov: 56, solarAltitude: 32, solarAzimuth: initialAzimuth, exposure: 0.87, cloudRange: 50 },
    above: { label: '从云上俯瞰', altitude: marineBands ? 4.7 : 13.5, pitch: -0.27, fov: 59, solarAltitude: 32, solarAzimuth: initialAzimuth, exposure: 0.88, cloudRange: 65 },
    dusk: { label: '海面暮光', altitude: minAltitude, pitch: 0.055, fov: 53, solarAltitude: 3, solarAzimuth: directionDegrees(start.yaw - 0.13), exposure: 0.79, cloudRange: 50 }
  };
}
function landmark(start) {
  return [start.x + 0.24 * Math.sin(start.yaw) + 0.082 * Math.cos(start.yaw),
    start.z + 0.24 * Math.cos(start.yaw) - 0.082 * Math.sin(start.yaw)];
}
let views = makeViews(activeDataset);
const state = { ...views.sea, ...initial, span: activeDataset.spanKm,
  island: landmark(initial), islandHeading: initial.yaw,
  time: 0, coverage: 1, thickness: 1, diffusion: 1, debug: 0, layers: 0, quality: 'auto' };
let selectedView = 'sea';
let selectedMap = 0;
let paused = matchMedia('(prefers-reduced-motion: reduce)').matches;
let immersive = false;
let renderer;
let frame = 0;
let lastTime;
let settle = 9;
let mapRequest = 0;
let initialization = 0;
const cachedMaps = new Map();
const keys = new Set();
const pointers = new Map();
let pinch = 0;

function altitudeText(km) {
  return km < 1 ? Math.round(km * 1000) + ' m' : km.toFixed(1) + ' km';
}

function placePin() {
  pin.style.left = (50 + 100 * state.x / state.span) + '%';
  pin.style.top = (50 + 100 * state.z / state.span) + '%';
  pin.style.transform = 'translate(-50%, -50%) rotate(' + (180 - state.yaw * degrees) + 'deg)';
}

function syncControls() {
  const height = altitudeText(state.altitude);
  byId('height-label').textContent = height;
  byId('view-label').textContent = Math.abs(state.altitude - views[selectedView].altitude) < 0.0001
    ? views[selectedView].label : '自定义高度';
  byId('altitude-value').textContent = height;
  byId('altitude').value = Math.round(1000 * Math.sqrt((state.altitude - minAltitude) / altitudeRange));
  byId('altitude').setAttribute('aria-valuetext', height);
  for (const [name, given] of [['solar', state.solarAltitude], ['azimuth', state.solarAzimuth]]) {
    const input = byId(name);
    const angle = String(given).replace('-', '−') + '°';
    input.value = given;
    byId(name + '-value').textContent = angle;
    input.setAttribute('aria-valuetext', angle);
  }
  for (const button of presetButtons) button.setAttribute('aria-pressed', button.dataset.view === selectedView);
  pause.textContent = paused ? '继续风场' : '暂停风场';
  pause.setAttribute('aria-pressed', paused);
  placePin();
}

function setStatus(message) {
  status.textContent = message;
  status.hidden = !message;
}

function queue() {
  if (!frame && renderer && !document.hidden) frame = requestAnimationFrame(draw);
}

function invalidate() {
  settle = 9;
  queue();
}

function choose(name, resetAtStart = false) {
  const view = views[name];
  selectedView = name;
  Object.assign(state, view);
  if (resetAtStart) {
    state.x = initial.x;
    state.z = initial.z;
  }
  state.yaw = initial.yaw;
  syncControls();
  invalidate();
}

async function paintMap(layer) {
  selectedMap = layer;
  const request = ++mapRequest;
  for (const button of mapTabs) button.setAttribute('aria-pressed', Number(button.dataset.map) === layer);
  satellite.hidden = layer !== 0;
  weatherMap.hidden = layer === 0;
  if (layer === 0) return;
  const filename = layer === 1 ? activeDataset.lowTexture ?? 'weather-lo.png'
    : activeDataset.highTexture ?? 'weather-hi.png';
  const { width, height } = weatherMap;
  const ctx = weatherMap.getContext('2d');
  try {
    if (!cachedMaps.has(filename)) {
      const response = await fetch(new URL(filename, import.meta.url));
      if (!response.ok) throw new Error(filename + ' ' + response.status);
      const bitmap = await createImageBitmap(await response.blob(),
        { premultiplyAlpha: 'none', colorSpaceConversion: 'none' });
      const scratch = document.createElement('canvas');
      scratch.width = width;
      scratch.height = height;
      const pixels = scratch.getContext('2d', { willReadFrequently: true });
      pixels.drawImage(bitmap, 0, 0, width, height);
      bitmap.close();
      const raw = pixels.getImageData(0, 0, width, height);
      for (let i = 0; i < raw.data.length; i += 4) {
        const coverage = raw.data[i] / 255;
        const cloudType = raw.data[i + 1] / 255;
        const t = Math.pow(coverage, 0.68);
        const low = layer === 1;
        raw.data[i] = 15 + t * (low ? 120 + 112 * cloudType : 119 + 104 * cloudType);
        raw.data[i + 1] = 32 + t * (low ? 177 + 32 * cloudType : 137 + 58 * cloudType);
        raw.data[i + 2] = 47 + t * (low ? 171 + 5 * cloudType : 198);
        raw.data[i + 3] = 255;
      }
      cachedMaps.set(filename, raw);
    }
    if (request === mapRequest && selectedMap === layer) ctx.putImageData(cachedMaps.get(filename), 0, 0);
  } catch (error) {
    console.error(error);
    if (request === mapRequest) paintMap(0);
  }
}

function move(dt) {
  if (!keys.size || dt <= 0) return;
  const { forward, right } = cameraBasis(state.yaw, 0);
  const speed = dt * (keys.has('Shift') ? 16 : 0.085 + state.altitude * 0.72);
  const a = Number(keys.has('w')) - Number(keys.has('s'));
  const b = Number(keys.has('d')) - Number(keys.has('a'));
  const edge = state.span * 0.488;
  state.x = clamp(state.x + (a * forward[0] + b * right[0]) * speed, -edge, edge);
  state.z = clamp(state.z + (a * forward[2] + b * right[2]) * speed, -edge, edge);
  const climb = Number(keys.has('e')) - Number(keys.has('q'));
  state.altitude = clamp(state.altitude + climb * dt * (0.56 + state.altitude * 0.42), minAltitude, 15);
  state.yaw += (Number(keys.has('ArrowRight')) - Number(keys.has('ArrowLeft'))) * dt * 0.94;
  state.pitch = clamp(state.pitch + (Number(keys.has('ArrowUp')) - Number(keys.has('ArrowDown'))) * dt * 0.89, -1.27, 1.33);
  syncControls();
}

function draw(now) {
  frame = 0;
  if (!renderer || document.hidden) return;
  const elapsed = lastTime === undefined ? 16.7 : now - lastTime;
  lastTime = now;
  const dt = Math.min(0.075, elapsed / 1000);
  move(dt);
  if (!paused) state.time += dt;
  renderer.draw(state, paused && !keys.size ? 0 : elapsed);
  const moving = !paused || keys.size;
  if (!moving) settle--;
  if (moving || settle > 0) queue();
}

async function init() {
  const generation = ++initialization;
  try {
    const next = await createCloudRenderer(canvas, activeDataset);
    if (generation !== initialization) return;
    next.draw(state, 0);
    renderer = next;
    datasetInput.disabled = false;
    setStatus('');
    invalidate();
  } catch (error) {
    if (generation !== initialization) return;
    renderer = undefined;
    console.error('体积云子项目', error);
    setStatus('体积云未能启动。请确认浏览器支持 WebGL 2，并重新加载页面。');
  }
}

function displayDataset(data) {
  byId('span-label').textContent = data.spanKm + ' × ' + data.spanKm + ' km';
  byId('weather-label').textContent = data.detail.split(' · ')[0];
  byId('weather-detail').textContent = data.detail + '。' + data.notes;
  byId('data-link').href = data.sourceUrl;
  satellite.src = data.preview ?? 'satellite.jpg';
  satellite.alt = data.label + '的云场观测';
  void paintMap(0);
}

for (const [i, data] of datasets.entries()) datasetInput.add(new Option(data.label, i));
byId('dataset-picker').hidden = false;
datasetInput.addEventListener('change', async event => {
  if (!renderer) return;
  const next = datasets[Number(event.currentTarget.value)];
  const request = ++datasetRequest;
  setStatus('正在切换卫星观测…');
  try {
    if (!await renderer.setWeather(next) || request !== datasetRequest) return;
    activeDataset = next;
    initial = next.start;
    views = makeViews(next);
    state.span = activeDataset.spanKm;
    state.island = landmark(initial);
    state.islandHeading = initial.yaw;
    state.time = 0;
    displayDataset(activeDataset);
    choose('sea', true);
    setStatus('');
  } catch (error) {
    if (request !== datasetRequest) return;
    console.error(error);
    datasetInput.value = datasets.indexOf(activeDataset);
    setStatus('所选卫星观测加载失败。');
  }
});
displayDataset(activeDataset);
for (const button of presetButtons) button.addEventListener('click', () => choose(button.dataset.view));
for (const button of mapTabs) button.addEventListener('click', () => { void paintMap(Number(button.dataset.map)); });
byId('reset-view').addEventListener('click', () => choose(selectedView, true));
map.addEventListener('click', event => {
  if (!event.detail) {
    state.x = initial.x;
    state.z = initial.z;
  } else {
    const bounds = map.getBoundingClientRect();
    const x = clamp((event.clientX - bounds.left) / bounds.width, 0.015, 0.985);
    const z = clamp((event.clientY - bounds.top) / bounds.height, 0.015, 0.985);
    state.x = (x - 0.5) * state.span;
    state.z = (z - 0.5) * state.span;
  }
  placePin();
  invalidate();
});

byId('altitude').addEventListener('input', event => {
  const input = Number(event.currentTarget.value) / 1000;
  state.altitude = minAltitude + altitudeRange * input ** 2;
  syncControls();
  invalidate();
});
for (const [id, key] of [['solar', 'solarAltitude'], ['azimuth', 'solarAzimuth']]) {
  byId(id).addEventListener('input', event => {
    state[key] = Number(event.currentTarget.value);
    syncControls();
    invalidate();
  });
}
for (const [id, key] of [['layers', 'layers'], ['lighting', 'debug'], ['quality', 'quality']]) {
  byId(id).addEventListener('change', event => {
    state[key] = key === 'quality' ? event.currentTarget.value : Number(event.currentTarget.value);
    invalidate();
  });
}
byId('diffusion').addEventListener('change', event => {
  state.diffusion = Number(event.currentTarget.checked);
  invalidate();
});
pause.addEventListener('click', () => {
  paused = !paused;
  lastTime = undefined;
  syncControls();
  invalidate();
});

const moveKeys = new Set(['w','a','s','d','q','e','Shift','ArrowLeft','ArrowRight','ArrowUp','ArrowDown']);
const normalizedKey = key => key.length === 1 ? key.toLowerCase() : key;
canvas.addEventListener('keydown', event => {
  const key = normalizedKey(event.key);
  if (!moveKeys.has(key)) return;
  event.preventDefault();
  if (!keys.size) lastTime = undefined;
  keys.add(key);
  invalidate();
});
window.addEventListener('keyup', event => keys.delete(normalizedKey(event.key)));
window.addEventListener('blur', () => keys.clear());
canvas.addEventListener('blur', () => keys.clear());

canvas.addEventListener('pointerdown', event => {
  if (event.button !== 0) return;
  canvas.focus({ preventScroll: true });
  canvas.setPointerCapture(event.pointerId);
  pointers.set(event.pointerId, [event.clientX, event.clientY]);
});
canvas.addEventListener('pointermove', event => {
  const before = pointers.get(event.pointerId);
  if (!before) return;
  pointers.set(event.pointerId, [event.clientX, event.clientY]);
  if (pointers.size === 2) {
    const [a, b] = pointers.values();
    const distance = Math.hypot(a[0] - b[0], a[1] - b[1]);
    if (pinch > 5 && distance > 5) state.fov = clamp(state.fov * pinch / distance, 30, 79);
    pinch = distance;
  } else {
    state.yaw -= (event.clientX - before[0]) * 0.0041;
    state.pitch = clamp(state.pitch + (event.clientY - before[1]) * 0.0041, -1.27, 1.33);
    placePin();
  }
  invalidate();
});
function releasePointer(event) {
  pointers.delete(event.pointerId);
  pinch = 0;
}
for (const name of ['pointerup', 'pointercancel', 'lostpointercapture']) canvas.addEventListener(name, releasePointer);
canvas.addEventListener('wheel', event => {
  event.preventDefault();
  state.fov = clamp(state.fov + event.deltaY * 0.035, 30, 79);
  invalidate();
}, { passive: false });

function setImmersive(enabled) {
  immersive = enabled;
  viewport.classList.toggle('immersive', enabled);
  enter.setAttribute('aria-pressed', enabled);
  exit.hidden = !enabled;
  panel.inert = enabled;
  byId('presets').inert = enabled;
  document.querySelector('.masthead').inert = enabled;
  document.querySelector('.footer').inert = enabled;
  document.body.style.overflow = enabled ? 'hidden' : '';
  (enabled ? exit : enter).focus({ preventScroll: true });
  invalidate();
}

enter.addEventListener('click', () => setImmersive(true));
exit.addEventListener('click', () => setImmersive(false));
document.addEventListener('keydown', event => {
  if (event.key === 'Escape' && immersive) setImmersive(false);
});
canvas.addEventListener('webglcontextlost', event => {
  event.preventDefault();
  initialization++;
  renderer = undefined;
  datasetInput.disabled = true;
  setStatus('渲染已中断，正在等待浏览器恢复…');
});
canvas.addEventListener('webglcontextrestored', init);
document.addEventListener('visibilitychange', () => {
  lastTime = undefined;
  invalidate();
});
new ResizeObserver(invalidate).observe(viewport);
syncControls();
void init();
