/* Exercise the production controller with browser/renderer boundary doubles. */
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const source = fs.readFileSync(path.join(__dirname, '../opening.js'), 'utf8');
const boundary = source.indexOf('  const paint=');
assert.ok(boundary > 0, 'controller boundary exists');

function setup(mode) {
  class Element {
    constructor() {
      this.dataset = {}; this.style = {setProperty() {}}; this.hidden = true; this.open = true; this.children = new Map(); this.listeners = new Map();
      const values = new Set();
      this.classList = { add: (...x) => x.forEach(v => values.add(v)), remove: (...x) => x.forEach(v => values.delete(v)), contains: x => values.has(x), toggle: (x, on) => on ? values.add(x) : values.delete(x) };
    }
    querySelector(selector) { if (!this.children.has(selector)) this.children.set(selector, new Element()); return this.children.get(selector); }
    querySelectorAll() { return []; }
    addEventListener(name, fn) { this.listeners.set(name, fn); }
    setAttribute() {} focus() {} contains(other) { return other === this; }
    close() { this.open = false; } showModal() { this.open = true; }
  }
  const elements = new Map();
  const document = new Element();
  document.getElementById = id => { if (!elements.has(id)) elements.set(id, new Element()); return elements.get(id); };
  document.body = new Element(); document.documentElement = new Element();
  document.fullscreenElement = null; document.fullscreenEnabled = mode !== 'disabled';
  const root = document.getElementById('symmetry-particle-studies');
  const dialog = document.getElementById('courseOpening');
  const counts = { play: 0, stop: 0, finish: 0, audioStart: 0, audioStop: 0, request: 0, exit: 0 };
  let resolve, reject;
  const change = () => document.listeners.get('fullscreenchange')();
  document.exitFullscreen = () => { counts.exit++; document.fullscreenElement = null; change(); return Promise.resolve(); };
  if (mode !== 'missing') root.requestFullscreen = () => {
    counts.request++;
    if (mode === 'throw') throw new Error('Fullscreen unavailable');
    if (mode === 'reject') return Promise.reject(new Error('Permission denied'));
    return new Promise((yes, no) => { resolve = yes; reject = no; });
  };
  const boot = { ready() {}, start() {dialog.open = true;}, stop() {}, finish() { counts.finish++; } };
  const context = {
    document, matchMedia: () => ({matches: false}), localStorage: {getItem: () => null},
    setTimeout: () => 0, clearTimeout() {}, Promise,
    window: {CourseOpeningBoot: boot, CourseOpeningAudio: {start() {counts.audioStart++;}, stop() {counts.audioStop++;}}},
    renderer: {refresh() {},play() {counts.play++;}, stop() {counts.stop++;}},
  };
  vm.runInNewContext(source.slice(0, boundary) + `
    film=renderer;initialization=Promise.resolve();stage='ready';root.dataset.stage=stage;
    globalThis.testController={startAnimation,leaveOpening,openOpening,get stage(){return stage;}};
  })();`, context);
  return { ...context.testController, controller: context.testController, counts, document, root, dialog, change,
    settleSuccess() {document.fullscreenElement = root; change(); resolve();},
    settleFailure() {reject(new Error('Late rejection'));},
    toggle: document.getElementById('openingSettingsToggle') };
}
const flush = async () => { await Promise.resolve(); await Promise.resolve(); };
function assertPlaying(env) {
  assert.equal(env.controller.stage, 'playing');
  assert.equal(env.dialog.open, true);
  assert.equal(env.counts.play, 1);
  assert.equal(env.counts.finish, 1);
  assert.equal(env.counts.audioStart, 1);
  assert.equal(env.counts.audioStop, 0);
  assert.equal(env.toggle.disabled, false);
  assert.equal(env.dialog.classList.contains('opening-ready'), true);
}
(async () => {
  for (const mode of ['missing', 'disabled', 'throw', 'reject', 'pending']) {
    const env = setup(mode);
    env.controller.startAnimation();
    assertPlaying(env); // Must start synchronously, before any promise settles.
    await flush();
    assertPlaying(env);
    env.controller.startAnimation();
    assert.equal(env.counts.play, 1, 'repeated start never duplicates playback');
    env.change();
    assertPlaying(env); // A windowed fullscreenchange is not an exit command.
    if (mode === 'disabled') assert.equal(env.counts.request, 0);
    console.log(`PASS ${mode}: playback and controls remain active`);
  }
  const normal = setup('pending');
  normal.controller.startAnimation(); normal.settleSuccess(); await flush();
  assertPlaying(normal);
  normal.document.fullscreenElement = null; normal.change();
  assertPlaying(normal);
  assert.equal(normal.counts.stop, 0, 'leaving fullscreen does not stop the film');
  normal.dialog.listeners.get('cancel')({preventDefault(){}});
  assertPlaying(normal);
  normal.controller.leaveOpening();
  assert.equal(normal.controller.stage, 'closed');
  assert.equal(normal.counts.stop, 1);

  const late = setup('pending');
  late.controller.startAnimation(); late.controller.leaveOpening(); late.settleSuccess(); await flush();
  assert.equal(late.controller.stage, 'closed');
  assert.equal(late.dialog.open, false);
  assert.equal(late.counts.exit, 1, 'late fullscreen success is cleaned up after leaving');
  assert.equal(late.counts.play, 1);

  const replay = setup('pending');
  replay.controller.startAnimation(); replay.controller.leaveOpening(); await replay.controller.openOpening();
  replay.settleFailure(); await flush();
  assert.equal(replay.controller.stage, 'ready', 'late rejection cannot overwrite reopened state');
  replay.controller.startAnimation();
  assert.equal(replay.controller.stage, 'playing');
  assert.equal(replay.counts.play, 2, 'replay remains available');
  console.log('PASS successful fullscreen, explicit exit, late completion, and replay');
})().catch(error => { console.error(error); process.exitCode = 1; });
