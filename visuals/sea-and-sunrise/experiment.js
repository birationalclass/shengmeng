import { createRenderer } from './renderer.js';
import { createSoundscape } from './audio.js';

const steps = [
  { name: '光', english: 'LIGHT', caption: '先给像素一个数', formula: 'pixel = vec3(r, g, b)', duration: 6 },
  { name: '天', english: 'SKY', caption: '颜色随高度展开', formula: 'sky(y) = scatter(sunlight, air(y))', duration: 6 },
  { name: '日', english: 'SUN', caption: '从一个点向外发光', formula: 'glow ∝ 1 / d²', duration: 6 },
  { name: '海', english: 'SEA', caption: '一条波，叠成海', formula: 'h += a[i] · exp(sin(k[i]·x − ω[i]t) − 1)   i < 32', duration: 10 },
  { name: '云', english: 'CLOUDS', caption: '五层噪声叠成云', formula: 'cloud += noise(p · 2ⁱ) / 2ⁱ   i < 5', duration: 7 },
  { name: '时间', english: 'TIME', caption: '第一次日出', formula: 't → sun, sea, clouds', duration: 19 }
];

const alternatives = {
  1: { caption: '极光', formula: 'sky += aurora(t)' },
  2: { caption: '黑洞', formula: 'sun = black_hole' },
  3: { caption: '土星', formula: 'moon = saturn' }
};

const defaults = { time: 59, wind: 100, cloud: 78, yaw: 0, pitch: 0.183 };
const state = {
  ...defaults,
  stage: 5,
  scene: 0,
  build: 1,
  clock: 0,
  paused: matchMedia('(prefers-reduced-motion: reduce)').matches,
  demo: false
};

const byId = id => document.getElementById(id);
const canvas = byId('scene');
const viewport = byId('viewport');
const timeInput = byId('time');
const windInput = byId('wind');
const cloudInput = byId('cloud');
const demoButton = byId('demo');
const motionButton = byId('motion');
const audioButton = byId('audio');
const immersiveButton = byId('immersive');
const exitImmersiveButton = byId('exit-immersive');
const message = byId('render-message');
const stageButtons = [...document.querySelectorAll('[data-step]')];
const sceneButtons = [...document.querySelectorAll('[data-scene]')];
const mix = (from, to, progress) => from + (to - from) * progress;
const clamp = (x, low, high) => Math.min(high, Math.max(low, x));
const smooth = (low, high, x) => {
  const t = clamp((x - low) / (high - low), 0, 1);
  return t * t * (3 - 2 * t);
};

let render;
let request = 0;
let previousTime = 0;
let drag;
let immersive = false;
let soundscape;
let soundLoading = false;

function updateReadouts() {
  const minutes = 285 + Math.round(state.time);
  byId('time-value').textContent =
    String(Math.floor(minutes / 60)).padStart(2, '0') + ':' + String(minutes % 60).padStart(2, '0');
  byId('wind-value').textContent = (state.wind / 100).toFixed(2);
  byId('cloud-value').textContent = state.cloud + '%';
  timeInput.value = state.time;
  windInput.value = state.wind;
  cloudInput.value = state.cloud;
  timeInput.setAttribute('aria-valuetext', byId('time-value').textContent);
}

function syncControls() {
  const step = steps[state.stage];
  const current = alternatives[state.scene] ?? step;
  byId('frame-number').textContent = String(state.stage + 1).padStart(2, '0') + ' / 06';
  byId('frame-title').textContent = step.name;
  byId('frame-english').textContent = step.english;
  byId('caption').textContent = current.caption;
  byId('formula').textContent = current.formula;
  for (const button of stageButtons) button.setAttribute('aria-pressed', Number(button.dataset.step) === state.stage);
  for (const button of sceneButtons) button.setAttribute('aria-pressed', Number(button.dataset.scene) === state.scene);
  demoButton.setAttribute('aria-pressed', state.demo);
  demoButton.querySelector('span').textContent = state.demo ? '结束演示' : '播放六步';
  motionButton.setAttribute('aria-pressed', state.paused);
  motionButton.textContent = state.paused ? '继续' : '暂停';
  timeInput.disabled = state.scene === 1 || state.scene === 2;
  cloudInput.disabled = state.scene === 1;
  byId('live').dataset.paused = state.paused;
  byId('live-status').textContent = state.paused ? '已暂停' : '实时生成';
  updateReadouts();
}

function updateSound() {
  soundscape?.setParameters({
    wind: state.wind / 100,
    daylight: state.time / 150,
    scene: state.scene
  });
}

function chooseStage(stage, scene = 0, animate = true) {
  state.stage = stage;
  state.scene = scene;
  state.build = stage === 5 || state.paused || !animate ? 1 : 0;
  syncControls();
  updateSound();
  queueFrame();
}

function advanceBuild(dt) {
  state.clock += dt;
  if (state.build >= 1) return;
  state.build = Math.min(1, state.build + dt / steps[state.stage].duration);

  if (state.demo && state.stage === 5) {
    state.time = Math.round(mix(48, 123, smooth(0.11, 0.81, state.build)));
    updateReadouts();
    updateSound();
  }

  if (state.build < 1 || !state.demo) return;
  if (state.stage < 5) {
    chooseStage(state.stage + 1);
    state.build = 0;
  } else {
    state.demo = false;
    syncControls();
  }
}

function frameUniforms() {
  const { stage, build } = state;
  const seaBuild = stage === 3 ? smooth(0.20, 0.42, build) : Number(stage > 3);
  const gridBuild = stage === 3 ? 1 - smooth(0.55, 0.85, build) : 0;
  const cloudBuild = stage === 4 ? smooth(0.18, 0.72, build) : Number(stage > 4);
  const time = stage === 5 ? state.time : 55;
  const elevation = -0.104 + 0.002 * time;
  return {
    Clock: state.clock,
    Wind: state.wind / 100,
    Wave: stage === 3 ? mix(0.2, 1, smooth(0.22, 0.48, build)) : Number(stage > 3),
    Grid: gridBuild,
    Cloud: state.cloud / 100 * cloudBuild,
    Stage: stage,
    Build: build,
    Sky: stage === 1 ? smooth(0.0, 0.25, build) : Number(stage > 1),
    Bands: stage === 1 ? 1 - smooth(0.62, 0.99, build) : 0,
    Sun: stage === 2 ? smooth(0.08, 0.55, build) : Number(stage > 2),
    Sea: seaBuild,
    Trace: stage === 3 ? 1 - smooth(0.16, 0.36, build) : 0,
    Yaw: state.yaw,
    Pitch: state.pitch,
    Elevation: elevation,
    Scene: state.scene
  };
}

function draw(now) {
  request = 0;
  if (!render || document.hidden) return;
  const delta = previousTime ? now - previousTime : 0;
  previousTime = now;
  if (!state.paused) advanceBuild(Math.min(delta / 1000, 0.065));
  render(frameUniforms(), state.paused ? 0 : delta);
  if (!state.paused) queueFrame();
}

function queueFrame() {
  if (!request && render && !document.hidden) request = requestAnimationFrame(draw);
}

function initRenderer() {
  try {
    render = createRenderer(canvas);
    message.hidden = true;
    queueFrame();
  } catch (error) {
    console.error('海和日出试验：渲染器初始化失败', error);
    message.textContent = '当前浏览器无法启动 WebGL 海天渲染。';
    message.hidden = false;
  }
}

for (const button of stageButtons) {
  button.addEventListener('click', () => {
    state.demo = false;
    chooseStage(Number(button.dataset.step));
  });
}

for (const button of sceneButtons) {
  button.addEventListener('click', () => {
    state.demo = false;
    chooseStage(5, Number(button.dataset.scene));
  });
}

demoButton.addEventListener('click', () => {
  state.demo = !state.demo;
  if (state.demo) {
    state.paused = false;
    state.clock = 0;
    state.time = 48;
    state.yaw = defaults.yaw;
    state.pitch = defaults.pitch;
    chooseStage(0);
  } else {
    chooseStage(5);
  }
  previousTime = 0;
});

motionButton.addEventListener('click', () => {
  state.paused = !state.paused;
  previousTime = 0;
  syncControls();
  queueFrame();
});

timeInput.addEventListener('input', () => {
  state.time = Number(timeInput.value);
  state.demo = false;
  chooseStage(5, state.scene, false);
});

windInput.addEventListener('input', () => {
  state.wind = Number(windInput.value);
  state.demo = false;
  if (state.stage < 3) chooseStage(3, 0, false);
  syncControls();
  updateSound();
  queueFrame();
});

cloudInput.addEventListener('input', () => {
  state.cloud = Number(cloudInput.value);
  state.demo = false;
  if (state.stage < 4) chooseStage(4, 0, false);
  syncControls();
  queueFrame();
});

byId('reset').addEventListener('click', () => {
  Object.assign(state, defaults, { clock: 0, demo: false });
  chooseStage(5);
});

audioButton.addEventListener('click', async () => {
  if (soundLoading) return;
  soundLoading = true;
  const enable = audioButton.getAttribute('aria-pressed') !== 'true';
  try {
    if (!soundscape) {
      soundscape = createSoundscape();
      updateSound();
    }
    const active = await soundscape.setEnabled(enable);
    audioButton.setAttribute('aria-pressed', Boolean(active));
    audioButton.textContent = active ? '关闭声音' : '声音';
    if (enable && !active) audioButton.title = '当前浏览器无法播放程序音景';
  } catch (error) {
    console.error('海和日出试验：声音启动失败', error);
  } finally {
    soundLoading = false;
  }
});

function turnView(dx, dy) {
  state.yaw = clamp(state.yaw + dx, -0.74, 0.74);
  state.pitch = clamp(state.pitch + dy, -0.02, 0.37);
  queueFrame();
}

function resetView() {
  state.yaw = defaults.yaw;
  state.pitch = defaults.pitch;
  queueFrame();
}

canvas.addEventListener('pointerdown', event => {
  if (!event.isPrimary || event.button !== 0) return;
  drag = { id: event.pointerId, x: event.clientX, y: event.clientY };
  canvas.setPointerCapture(event.pointerId);
});

canvas.addEventListener('pointermove', event => {
  if (drag?.id !== event.pointerId) return;
  const scale = 1.8 / Math.max(360, canvas.clientWidth);
  turnView((drag.x - event.clientX) * scale, (event.clientY - drag.y) * scale);
  drag.x = event.clientX;
  drag.y = event.clientY;
});

canvas.addEventListener('lostpointercapture', () => { drag = undefined; });
canvas.addEventListener('dblclick', resetView);
canvas.addEventListener('keydown', event => {
  const keys = {
    ArrowLeft: [-0.065, 0], ArrowRight: [0.065, 0],
    ArrowUp: [0, 0.04], ArrowDown: [0, -0.04]
  };
  if (keys[event.key]) {
    event.preventDefault();
    turnView(...keys[event.key]);
  } else if (event.key === 'Home') {
    event.preventDefault();
    resetView();
  }
});

function setImmersive(enabled) {
  immersive = enabled;
  viewport.classList.toggle('is-immersive', enabled);
  immersiveButton.setAttribute('aria-pressed', enabled);
  byId('workbench').inert = enabled;
  document.querySelector('.masthead').inert = enabled;
  document.querySelector('.credit').inert = enabled;
  document.body.style.overflow = enabled ? 'hidden' : '';
  (enabled ? exitImmersiveButton : immersiveButton).focus({ preventScroll: true });
  queueFrame();
}

immersiveButton.addEventListener('click', () => setImmersive(true));
exitImmersiveButton.addEventListener('click', () => setImmersive(false));
document.addEventListener('keydown', event => {
  if (event.key === 'Escape' && immersive) setImmersive(false);
});

canvas.addEventListener('webglcontextlost', event => {
  event.preventDefault();
  render = undefined;
  message.textContent = '渲染已中断，正在恢复…';
  message.hidden = false;
});
canvas.addEventListener('webglcontextrestored', initRenderer);
document.addEventListener('visibilitychange', () => {
  previousTime = 0;
  queueFrame();
});
new ResizeObserver(queueFrame).observe(viewport);

syncControls();
initRenderer();
