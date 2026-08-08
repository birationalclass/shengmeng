import { mkdir, writeFile } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const sampleRate = 32000;
const bpm = 88;
const beat = 60 / bpm;
const bars = 8;
const duration = bars * 4 * beat;
const frames = Math.ceil(duration * sampleRate);
const left = new Float32Array(frames);
const right = new Float32Array(frames);
const midiHz = (note) => 440 * 2 ** ((note - 69) / 12);

function envelope(t, length, attack, release) {
  if (t < attack) return Math.sin((t / attack) * Math.PI * .5) ** 2;
  if (t > length - release) return Math.sin(((length - t) / release) * Math.PI * .5) ** 2;
  return 1;
}

function addTone(start, length, note, level, { pan = 0, attack = .01, release = .16, voice = "warm", decay = 0 } = {}) {
  const first = Math.max(0, Math.floor(start * sampleRate));
  const last = Math.min(frames, Math.ceil((start + length) * sampleRate));
  const frequency = midiHz(note);
  const panL = Math.cos((pan + 1) * Math.PI / 4);
  const panR = Math.sin((pan + 1) * Math.PI / 4);
  for (let i = first; i < last; i += 1) {
    const t = i / sampleRate - start;
    const phase = Math.PI * 2 * frequency * t;
    let value;
    if (voice === "bass") value = Math.sin(phase) + .22 * Math.sin(phase * 2) + .08 * Math.sin(phase * 3);
    else if (voice === "pluck") value = Math.sin(phase) + .3 * Math.sin(phase * 2) + .12 * Math.sin(phase * 4);
    else if (voice === "lead") value = Math.sin(phase) + .18 * Math.sin(phase * 2) + .07 * Math.sin(phase * 3);
    else value = Math.sin(phase) + .14 * Math.sin(phase * 2) + .04 * Math.sin(phase * 3);
    const shaped = value * envelope(t, length, attack, release) * (decay ? Math.exp(-t * decay) : 1) * level;
    left[i] += shaped * panL;
    right[i] += shaped * panR;
  }
}

function addKick(start, level = .22) {
  const length = .28;
  const first = Math.floor(start * sampleRate);
  const last = Math.min(frames, Math.ceil((start + length) * sampleRate));
  let phase = 0;
  for (let i = first; i < last; i += 1) {
    const t = i / sampleRate - start;
    const frequency = 92 * Math.exp(-t * 10) + 39;
    phase += Math.PI * 2 * frequency / sampleRate;
    const value = Math.sin(phase) * Math.exp(-t * 15) * level;
    left[i] += value * .72;
    right[i] += value * .72;
  }
}

function addRim(start, level = .055) {
  addTone(start, .09, 86, level, { pan: .18, attack: .002, release: .07, voice: "pluck", decay: 24 });
  addTone(start, .12, 74, level * .45, { pan: -.14, attack: .002, release: .1, voice: "pluck", decay: 18 });
}

const progression = [
  { root: 38, chord: [50, 53, 57] },
  { root: 34, chord: [46, 50, 53] },
  { root: 41, chord: [53, 57, 60] },
  { root: 36, chord: [48, 52, 55] },
  { root: 38, chord: [50, 53, 57] },
  { root: 34, chord: [46, 50, 53] },
  { root: 41, chord: [53, 57, 60] },
  { root: 36, chord: [48, 52, 55] }
];

progression.forEach((harmony, bar) => {
  const start = bar * 4 * beat;
  harmony.chord.forEach((note, index) => addTone(start, beat * 3.95, note, .034, { pan: (index - 1) * .52, attack: .42, release: .7, voice: "warm" }));
  const bassLine = [harmony.root, harmony.root, harmony.root + 7, harmony.root];
  bassLine.forEach((note, quarter) => addTone(start + quarter * beat, beat * .82, note, .105, { pan: -.06, attack: .018, release: .22, voice: "bass" }));
  const arp = [harmony.chord[0] + 12, harmony.chord[1] + 12, harmony.chord[2] + 12, harmony.chord[1] + 12, harmony.chord[0] + 12, harmony.chord[2] + 12, harmony.chord[1] + 12, harmony.chord[2] + 12];
  arp.forEach((note, eighth) => addTone(start + eighth * beat / 2, beat * .36, note, .025, { pan: eighth % 2 ? .45 : -.45, attack: .008, release: .16, voice: "pluck", decay: 2.4 }));
  addKick(start, .19);
  addRim(start + beat * 2, .048);
  if (bar >= 4) addKick(start + beat * 2.75, .115);
});

const melody = [
  [0.5, .75, 69], [1.5, .5, 72], [2.25, 1.1, 74],
  [4.5, .7, 70], [5.5, .5, 69], [6.25, 1.15, 65],
  [8.5, .7, 69], [9.5, .45, 72], [10.15, .45, 77], [10.85, .85, 76],
  [12.5, .75, 67], [13.5, .5, 64], [14.25, 1.15, 62],
  [16.25, .5, 69], [17, .5, 72], [17.75, .5, 74], [18.5, 1.15, 77],
  [20.5, .7, 74], [21.5, .5, 70], [22.25, 1.1, 69],
  [24.5, .7, 72], [25.5, .45, 74], [26.15, .45, 77], [26.85, .85, 81],
  [28.5, .65, 79], [29.35, .45, 76], [30.05, .45, 74], [30.75, .95, 69]
];
melody.forEach(([atBeat, beatsLong, note], index) => addTone(atBeat * beat, beatsLong * beat, note, .052, { pan: index % 3 === 0 ? -.18 : .2, attack: .035, release: .24, voice: "lead" }));

for (let delay = .31; delay <= .93; delay += .31) {
  const gain = .08 * (1 - delay / 1.3);
  for (let i = Math.floor(delay * sampleRate); i < frames; i += 1) {
    left[i] += right[i - Math.floor(delay * sampleRate)] * gain;
    right[i] += left[i - Math.floor(delay * sampleRate)] * gain;
  }
}

let peak = 0;
for (let i = 0; i < frames; i += 1) {
  const edge = Math.min(1, i / (sampleRate * .06), (frames - 1 - i) / (sampleRate * .08));
  left[i] = Math.tanh(left[i] * 1.12) * Math.max(0, edge);
  right[i] = Math.tanh(right[i] * 1.12) * Math.max(0, edge);
  peak = Math.max(peak, Math.abs(left[i]), Math.abs(right[i]));
}
const scale = .88 / Math.max(.001, peak);

const dataBytes = frames * 2 * 2;
const buffer = Buffer.alloc(44 + dataBytes);
buffer.write("RIFF", 0); buffer.writeUInt32LE(36 + dataBytes, 4); buffer.write("WAVE", 8);
buffer.write("fmt ", 12); buffer.writeUInt32LE(16, 16); buffer.writeUInt16LE(1, 20); buffer.writeUInt16LE(2, 22);
buffer.writeUInt32LE(sampleRate, 24); buffer.writeUInt32LE(sampleRate * 4, 28); buffer.writeUInt16LE(4, 32); buffer.writeUInt16LE(16, 34);
buffer.write("data", 36); buffer.writeUInt32LE(dataBytes, 40);
for (let i = 0; i < frames; i += 1) {
  buffer.writeInt16LE(Math.max(-32768, Math.min(32767, Math.round(left[i] * scale * 32767))), 44 + i * 4);
  buffer.writeInt16LE(Math.max(-32768, Math.min(32767, Math.round(right[i] * scale * 32767))), 46 + i * 4);
}

const here = dirname(fileURLToPath(import.meta.url));
const output = resolve(here, "..", "assets", "endless-theme.wav");
await mkdir(dirname(output), { recursive: true });
await writeFile(output, buffer);
console.log(JSON.stringify({ output, duration: duration.toFixed(2), sampleRate, channels: 2, bytes: buffer.length }));
