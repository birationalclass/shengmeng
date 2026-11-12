const harmonies = [
  [[38, 50, 57, 64], [33, 49, 57, 66], [35, 50, 57, 64], [31, 47, 54, 62]],
  [[38, 48, 53, 64], [34, 48, 53, 62], [31, 46, 57, 62], [36, 48, 55, 65]],
  [[33, 45, 52, 58], [33, 46, 52, 60], [31, 43, 50, 58], [33, 45, 53, 59]],
  [[40, 51, 56, 66], [36, 48, 55, 64], [37, 49, 56, 63], [33, 49, 56, 64]],
];

function surfNoise(context) {
  const buffer = context.createBuffer(2, context.sampleRate * 4, context.sampleRate);
  let random = 13807;
  for (let channel = 0; channel < buffer.numberOfChannels; channel++) {
    const samples = buffer.getChannelData(channel);
    for (let i = 0; i < samples.length; i++) {
      random = (Math.imul(1664525, random) + 1013904223) >>> 0;
      samples[i] = random / 2147483648 - 1;
    }
  }
  return buffer;
}

function modulation(context, frequency, depth, parameter) {
  const oscillator = context.createOscillator();
  const gain = context.createGain();
  oscillator.frequency.value = frequency;
  gain.gain.value = depth;
  oscillator.connect(gain).connect(parameter);
  oscillator.start();
}

function buildAudio(context) {
  const output = context.createGain();
  output.gain.value = 0;
  output.connect(context.destination);

  const surf = context.createBufferSource();
  const rumbleFilter = context.createBiquadFilter();
  const surfFilter = context.createBiquadFilter();
  const swell = context.createGain();
  surf.buffer = surfNoise(context);
  surf.loop = true;
  rumbleFilter.type = 'highpass';
  rumbleFilter.frequency.value = 55;
  surfFilter.frequency.value = 430;
  swell.gain.value = 0.13;
  surf.connect(rumbleFilter).connect(surfFilter).connect(swell).connect(output);
  modulation(context, 0.14, 0.055, swell.gain);
  modulation(context, 0.092, 0.028, swell.gain);
  surf.start();

  const tone = context.createBiquadFilter();
  const score = context.createGain();
  const overtones = context.createPeriodicWave(
    new Float32Array(6),
    new Float32Array([0, 1, 0.36, 0.16, 0.06, 0.035]),
  );
  tone.frequency.value = 540;
  tone.connect(score).connect(output);
  const voices = harmonies[0][0].map((note, index) => {
    const oscillator = context.createOscillator();
    const gain = context.createGain();
    oscillator.frequency.value = 440 * 2 ** ((note - 69) / 12);
    if (index > 0) oscillator.setPeriodicWave(overtones);
    gain.gain.value = [0.086, 0.05, 0.043, 0.032][index];
    oscillator.connect(gain).connect(tone);
    modulation(context, 0.058 + 0.027 * index, 0.012, gain.gain);
    oscillator.start();
    return oscillator;
  });
  return { context, output, surfFilter, swell, tone, score, voices };
}

export function createSoundscape() {
  const parameters = { wind: 1, daylight: 0.35, scene: 0 };
  const applied = { wind: -1, daylight: -1, scene: -1 };
  let audio;
  let revision = 0;
  let scoreTimer;
  let sleepTimer;
  let playingHarmony;

  function updateHarmony() {
    const now = audio.context.currentTime;
    const progression = harmonies[parameters.scene];
    const chord = progression[Math.floor(now / 7.2) % progression.length];
    if (chord === playingHarmony) return;
    playingHarmony = chord;
    audio.voices.forEach((voice, index) => {
      const frequency = 440 * 2 ** ((chord[index] - 69) / 12);
      voice.frequency.setTargetAtTime(frequency, now, 0.12);
    });
  }

  function setParameters(next) {
    if (Number.isFinite(next.wind)) parameters.wind = Math.max(0, Math.min(2, next.wind));
    if (Number.isFinite(next.daylight)) parameters.daylight = Math.max(0, Math.min(1, next.daylight));
    if (Number.isInteger(next.scene) && harmonies[next.scene]) parameters.scene = next.scene;
    if (!audio) return;
    const { wind, daylight, scene } = parameters;
    if (Math.abs(wind - applied.wind) < 0.01 &&
        Math.abs(daylight - applied.daylight) < 0.005 &&
        scene === applied.scene) return;
    Object.assign(applied, parameters);
    const now = audio.context.currentTime;
    audio.surfFilter.frequency.setTargetAtTime(220 + wind * 255 + daylight * 110, now, 0.45);
    audio.swell.gain.setTargetAtTime(0.09 + wind * 0.09, now, 0.55);
    audio.tone.frequency.setTargetAtTime((scene === 2 ? 290 : 430) + 520 * daylight, now, 0.65);
    audio.score.gain.setTargetAtTime(0.37 + daylight * 0.26, now, 0.85);
    updateHarmony();
  }

  async function setEnabled(nextEnabled) {
    const attempt = ++revision;
    clearTimeout(sleepTimer);
    clearInterval(scoreTimer);
    if (!nextEnabled) {
      if (audio) {
        audio.output.gain.setTargetAtTime(0, audio.context.currentTime, 0.095);
        sleepTimer = setTimeout(() => {
          if (attempt === revision) audio.context.suspend().catch(() => {});
        }, 650);
      }
      return false;
    }

    const AudioContext = globalThis.AudioContext || globalThis.webkitAudioContext;
    if (!AudioContext) return false;
    try {
      if (!audio) {
        let context;
        try {
          context = new AudioContext({ sampleRate: 48000 });
        } catch {
          context = new AudioContext();
        }
        try {
          audio = buildAudio(context);
          setParameters(parameters);
        } catch (error) {
          audio = undefined;
          context.close().catch(() => {});
          throw error;
        }
      }
      await audio.context.resume();
      if (attempt !== revision || audio.context.state !== 'running') return false;
      audio.output.gain.setTargetAtTime(0.66, audio.context.currentTime, 0.24);
      updateHarmony();
      scoreTimer = setInterval(updateHarmony, 400);
      return true;
    } catch {
      return false;
    }
  }

  return { setEnabled, setParameters };
}
