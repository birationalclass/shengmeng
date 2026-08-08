import { mkdir, writeFile } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const sampleRate = 24000;
const bpm = 96;
const beat = 60 / bpm;
const barLength = beat * 4;
const bars = 48;
const duration = bars * barLength;
const frames = Math.ceil(duration * sampleRate);
const left = new Float32Array(frames);
const right = new Float32Array(frames);
const midiHz = (note) => 440 * 2 ** ((note - 69) / 12);

function env(t, length, attack, release) {
  if (t < attack) return Math.sin((t / attack) * Math.PI * .5) ** 2;
  if (t > length - release) return Math.sin(((length - t) / release) * Math.PI * .5) ** 2;
  return 1;
}

function addTone(start, length, note, level, { pan = 0, attack = .01, release = .12, voice = "warm", decay = 0, vibrato = 0 } = {}) {
  const first = Math.max(0, Math.floor(start * sampleRate));
  const last = Math.min(frames, Math.ceil((start + length) * sampleRate));
  const frequency = midiHz(note);
  const panL = Math.cos((pan + 1) * Math.PI / 4);
  const panR = Math.sin((pan + 1) * Math.PI / 4);
  for (let i = first; i < last; i += 1) {
    const t = i / sampleRate - start;
    const bend = vibrato ? 1 + Math.sin(Math.PI * 2 * 5.1 * t) * vibrato : 1;
    const phase = Math.PI * 2 * frequency * t * bend;
    let value;
    if (voice === "bass") value = Math.sin(phase) + .28 * Math.sin(phase * 2) + .12 * Math.sin(phase * 3);
    else if (voice === "arp") value = Math.sin(phase) + .34 * Math.sin(phase * 2) + .14 * Math.sin(phase * 4);
    else if (voice === "lead") value = Math.sin(phase) + .2 * Math.sin(phase * 2) + .08 * Math.sin(phase * 3);
    else if (voice === "brass") value = Math.sin(phase) + .22 * Math.sin(phase * 3) + .09 * Math.sin(phase * 5);
    else value = Math.sin(phase) + .13 * Math.sin(phase * 2) + .045 * Math.sin(phase * 3);
    const sample = value * env(t, length, attack, release) * (decay ? Math.exp(-t * decay) : 1) * level;
    left[i] += sample * panL;
    right[i] += sample * panR;
  }
}

function addKick(start, level = .18) {
  const length = .3;
  const first = Math.floor(start * sampleRate);
  const last = Math.min(frames, Math.ceil((start + length) * sampleRate));
  let phase = 0;
  for (let i = first; i < last; i += 1) {
    const t = i / sampleRate - start;
    const frequency = 104 * Math.exp(-t * 13) + 38;
    phase += Math.PI * 2 * frequency / sampleRate;
    const sample = Math.sin(phase) * Math.exp(-t * 14) * level;
    left[i] += sample * .72;
    right[i] += sample * .72;
  }
}

function addSnare(start, level = .06) {
  const length = .18;
  const first = Math.floor(start * sampleRate);
  const last = Math.min(frames, Math.ceil((start + length) * sampleRate));
  let seed = ((first + 1) * 1664525 + 1013904223) >>> 0;
  let previous = 0;
  for (let i = first; i < last; i += 1) {
    const t = i / sampleRate - start;
    seed = (seed * 1664525 + 1013904223) >>> 0;
    const raw = seed / 0xffffffff * 2 - 1;
    const bright = raw - previous * .86;
    previous = raw;
    const body = Math.sin(Math.PI * 2 * 178 * t) * .45;
    const sample = (bright * .42 + body) * Math.exp(-t * 24) * level;
    left[i] += sample * .67;
    right[i] += sample * .74;
  }
}

function addHat(start, level = .018, pan = 0) {
  const length = .065;
  const first = Math.floor(start * sampleRate);
  const last = Math.min(frames, Math.ceil((start + length) * sampleRate));
  const panL = Math.cos((pan + 1) * Math.PI / 4);
  const panR = Math.sin((pan + 1) * Math.PI / 4);
  for (let i = first; i < last; i += 1) {
    const t = i / sampleRate - start;
    const metallic = Math.sin(Math.PI * 2 * 5100 * t) + .55 * Math.sin(Math.PI * 2 * 7310 * t) + .25 * Math.sin(Math.PI * 2 * 9040 * t);
    const sample = metallic * Math.exp(-t * 58) * level;
    left[i] += sample * panL;
    right[i] += sample * panR;
  }
}

function addTom(start, note, level = .08, pan = 0) {
  addTone(start, .34, note, level, { pan, attack: .004, release: .25, voice: "bass", decay: 7 });
}

function addRiser(start, length, level = .018) {
  const first = Math.floor(start * sampleRate);
  const last = Math.min(frames, Math.ceil((start + length) * sampleRate));
  let phase = 0;
  for (let i = first; i < last; i += 1) {
    const t = i / sampleRate - start;
    const progress = t / length;
    const frequency = 110 + progress ** 2 * 540;
    phase += Math.PI * 2 * frequency / sampleRate;
    const sample = Math.sin(phase) * Math.sin(progress * Math.PI) ** 2 * level;
    left[i] += sample * .62;
    right[i] += sample * .78;
  }
}

const harmonies = {
  Dm: { root: 38, chord: [50, 53, 57] },
  Bb: { root: 34, chord: [46, 50, 53] },
  F: { root: 41, chord: [53, 57, 60] },
  C: { root: 36, chord: [48, 52, 55] },
  A: { root: 33, chord: [45, 49, 52] },
  Gm: { root: 31, chord: [43, 46, 50] }
};

const progression = [
  "Dm", "Dm", "Bb", "Bb", "F", "F", "C", "A",
  "Dm", "Bb", "F", "C", "Dm", "Bb", "F", "C", "Dm", "Bb", "F", "C", "Dm", "Bb", "F", "A",
  "Gm", "Bb", "Dm", "A", "Gm", "Bb", "C", "A",
  "Dm", "C", "Bb", "A", "Dm", "F", "C", "A", "Dm", "Bb", "F", "A",
  "Dm", "Bb", "A", "Dm"
];

progression.forEach((name, bar) => {
  const harmony = harmonies[name];
  const start = bar * barLength;
  const intro = bar < 8;
  const combatA = bar >= 8 && bar < 24;
  const breakSection = bar >= 24 && bar < 32;
  const combatB = bar >= 32 && bar < 44;
  const outro = bar >= 44;
  const padLevel = breakSection ? .033 : intro || outro ? .028 : .024;

  harmony.chord.forEach((note, index) => addTone(start, barLength * .98, note, padLevel, { pan: (index - 1) * .58, attack: intro || breakSection ? .48 : .2, release: .62, voice: "warm" }));

  if (intro) {
    [0, 2].forEach((position, index) => addTone(start + position * beat, beat * 1.65, index ? harmony.root + 7 : harmony.root, .082, { pan: -.08, attack: .035, release: .36, voice: "bass" }));
    addKick(start, .12);
    if (bar % 2 === 1) addSnare(start + beat * 3, .032);
    [1, 3].forEach((position) => addTone(start + position * beat, beat * .55, harmony.chord[1] + 12, .014, { pan: .36, attack: .02, release: .25, voice: "arp", decay: 1.7 }));
  }

  if (combatA || combatB) {
    const bassPattern = combatB ? [0, 12, 0, 7, 0, 12, 7, 0] : [0, 0, 7, 0, 0, 12, 7, 0];
    bassPattern.forEach((offset, eighth) => addTone(start + eighth * beat / 2, beat * .39, harmony.root + offset, combatB ? .092 : .082, { pan: -.08, attack: .012, release: .14, voice: "bass" }));
    const arp = [0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 2, 1, 0, 2];
    arp.forEach((chordIndex, sixteenth) => addTone(start + sixteenth * beat / 4, beat * .19, harmony.chord[chordIndex] + 12, combatB ? .024 : .019, { pan: sixteenth % 2 ? .48 : -.48, attack: .005, release: .08, voice: "arp", decay: 4.2 }));
    const kicks = combatB ? [0, .75, 2, 2.75, 3.5] : [0, 1.5, 2.5];
    kicks.forEach((position, index) => addKick(start + position * beat, (combatB ? .18 : .165) * (index ? .82 : 1)));
    [1, 3].forEach((position) => addSnare(start + position * beat, combatB ? .058 : .05));
    for (let eighth = 0; eighth < 8; eighth += 1) addHat(start + eighth * beat / 2, combatB && eighth % 2 ? .021 : .014, eighth % 2 ? .38 : -.32);
  }

  if (breakSection) {
    [0, 2].forEach((position) => addTone(start + position * beat, beat * 1.55, harmony.root + (position ? 7 : 0), .073, { pan: -.1, attack: .03, release: .45, voice: "bass" }));
    addKick(start, .1);
    addTom(start + beat * 2.5, harmony.root + 12, .065, -.3);
    addTom(start + beat * 3.15, harmony.root + 7, .055, .28);
    [0, 1, 2, 1].forEach((index, quarter) => addTone(start + quarter * beat, beat * .46, harmony.chord[index] + 12, .016, { pan: quarter % 2 ? .4 : -.4, attack: .02, release: .25, voice: "arp", decay: 1.5 }));
  }

  if (outro) {
    [0, 2].forEach((position) => addTone(start + position * beat, beat * 1.5, harmony.root, .07, { pan: -.06, attack: .025, release: .45, voice: "bass" }));
    addKick(start, .105);
    if (bar < 47) addSnare(start + beat * 2, .032);
  }
});

function addPhrase(baseBar, notes, level = .05, transpose = 0) {
  notes.forEach(([atBeat, beatsLong, note], index) => addTone(baseBar * barLength + atBeat * beat, beatsLong * beat, note + transpose, level, { pan: index % 3 === 0 ? -.2 : .22, attack: .025, release: .25, voice: "lead", vibrato: .0012 }));
}

const combatMotif = [
  [.5, .55, 69], [1.25, .5, 72], [2, 1, 74], [3.5, .35, 69],
  [4.5, .55, 70], [5.25, .5, 69], [6, 1.1, 65],
  [8.5, .55, 69], [9.25, .5, 72], [10, .5, 77], [10.75, .8, 76],
  [12.5, .55, 67], [13.25, .5, 64], [14, 1.25, 62]
];
const assaultMotif = [
  [.25, .4, 74], [1, .4, 77], [1.75, .85, 81], [3, .5, 79],
  [4.25, .4, 77], [5, .4, 74], [5.75, .85, 72], [7, .5, 69],
  [8.25, .4, 74], [9, .4, 77], [9.75, .55, 81], [10.55, .55, 84],
  [12.25, .4, 82], [13, .4, 79], [13.75, .4, 77], [14.5, 1.05, 74]
];
addPhrase(2, [[.5, 1.2, 62], [2.25, .8, 65], [4.5, 1.2, 69], [6.25, .8, 67], [8.5, 1.2, 65], [10.25, .8, 64], [12.5, 1.4, 61]], .035);
addPhrase(8, combatMotif, .048);
addPhrase(12, combatMotif, .044, -2);
addPhrase(16, combatMotif, .052);
addPhrase(20, combatMotif, .047, 2);
addPhrase(24, [[.5, 1.3, 67], [2.25, .75, 70], [4.5, 1.3, 69], [6.25, .75, 65], [8.5, 1.3, 62], [10.25, .75, 65], [12.5, 1.5, 61]], .04);
addPhrase(32, assaultMotif, .052);
addPhrase(36, assaultMotif, .047, -2);
addPhrase(40, assaultMotif, .055);
addPhrase(44, [[.5, .8, 74], [1.75, .6, 72], [4.5, .8, 70], [5.75, .6, 69], [8.5, .8, 69], [9.75, .6, 65], [12.5, 1.6, 62]], .038);

for (let bar = 32; bar < 44; bar += 1) {
  const harmony = harmonies[progression[bar]];
  addTone(bar * barLength, beat * 1.8, harmony.chord[0], .025, { pan: -.52, attack: .08, release: .5, voice: "brass" });
  addTone(bar * barLength + beat * 2, beat * 1.7, harmony.chord[2], .022, { pan: .52, attack: .08, release: .45, voice: "brass" });
}

addRiser(7 * barLength, barLength, .015);
addRiser(31 * barLength, barLength, .02);
addRiser(43 * barLength, barLength, .012);
[7.45, 23.45, 31.45, 43.45].forEach((barPosition) => {
  addTom(barPosition * barLength, 50, .075, -.42);
  addTom(barPosition * barLength + beat * .55, 45, .07, .05);
  addTom(barPosition * barLength + beat * 1.05, 38, .08, .42);
});

for (const delay of [.29, .58, .87]) {
  const offset = Math.floor(delay * sampleRate);
  const gain = .075 * (1 - delay / 1.2);
  for (let i = offset; i < frames; i += 1) {
    const echoL = right[i - offset] * gain;
    const echoR = left[i - offset] * gain;
    left[i] += echoL;
    right[i] += echoR;
  }
}

let peak = 0;
for (let i = 0; i < frames; i += 1) {
  const edge = Math.min(1, i / (sampleRate * .08), (frames - 1 - i) / (sampleRate * .12));
  left[i] = Math.tanh(left[i] * 1.08) * Math.max(0, edge);
  right[i] = Math.tanh(right[i] * 1.08) * Math.max(0, edge);
  peak = Math.max(peak, Math.abs(left[i]), Math.abs(right[i]));
}
const scale = .9 / Math.max(.001, peak);
const dataBytes = frames * 4;
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
console.log(JSON.stringify({ output, title: "终线脉冲·战区版", duration: duration.toFixed(2), bpm, bars, sampleRate, channels: 2, bytes: buffer.length }));
