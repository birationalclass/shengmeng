const waveCount = 32;
const geometryWaveCount = 6;

const waveModes = Array.from({ length: waveCount }, (_, index) => {
  const capillary = Math.max(0, index - geometryWaveCount) / (waveCount - geometryWaveCount - 1);
  const angle = 0.84 * Math.sin(index * 2.39996323 + 0.14)
    + 0.28 * Math.sin(index * 0.79)
    + 0.38 * capillary * Math.sin(index * 1.423);
  const frequency = 0.61 * 1.157 ** index;
  const amplitude = 0.37 * 0.775 ** index * (1 + 1.15 * capillary);
  const angularSpeed = 0.44 * Math.sqrt(9.81 * frequency);
  const phase = (index * (3.721 + 0.263 * index) + 1.6) % (2 * Math.PI);

  return [Math.sin(angle) * frequency, Math.cos(angle) * frequency,
    angularSpeed, phase, amplitude, frequency].map(value => value.toFixed(7));
});

function waveTerm(index, shape = "1.0") {
  const [kx, kz, speed, phase, amplitude, frequency] = waveModes[index];
  return `seaMode(p, clock, vec4(${kx}, ${kz}, ${speed}, ${phase}),
    ${amplitude} * seaBandLimit(${frequency}, footprint), ${shape})`;
}

function waveBand(start, end) {
  return waveModes.slice(start, end).map((_, offset) => `+ ${waveTerm(start + offset)}`).join("\n      ");
}

// Water coordinates are world-space metres. Each mode returns height and
// both derivatives, so displaced geometry and glints share the same crests.
export const seaSource = `
float seaBandLimit(float waveNumber, float footprint) {
  return 1.0 - smoothstep(0.65, 2.25, waveNumber * footprint);
}

vec3 seaMode(vec2 p, float clock, vec4 mode, float amplitude, float shape) {
  float phase = dot(mode.xy, p) - mode.z * clock + mode.w;
  float sine = sin(phase);
  float crest = exp(sine - 1.0);
  // exp(sin(phase) - 1) has a mean of approximately 0.466.
  // Removing the mean holds the average ocean level at zero.
  float height = mix(sine, crest - 0.46576, shape);
  float slope = mix(1.0, crest, shape) * cos(phase);
  return amplitude * vec3(height, slope * mode.xy);
}

vec3 seaSwell(vec2 p, float clock, float footprint, vec3 weights) {
  vec3 first = ${waveTerm(0, "weights.y")};
  vec3 rest = vec3(0.0)
      ${waveBand(1, geometryWaveCount)};
  return weights.x * first + weights.z * rest;
}

vec3 seaRipples(vec2 p, float clock, float footprint) {
  vec3 ripples = vec3(0.0);
  // Short waves fall out as their wavelength approaches a pixel footprint.
  // Evaluate the bands that can contribute at the current distance.
  if (footprint < 1.55) {
    ripples += vec3(0.0)
      ${waveBand(geometryWaveCount, 13)};
  }
  if (footprint < 0.58) {
    ripples += vec3(0.0)
      ${waveBand(13, 20)};
  }
  if (footprint < 0.22) {
    ripples += vec3(0.0)
      ${waveBand(20, 26)};
  }
  if (footprint < 0.09) {
    ripples += vec3(0.0)
      ${waveBand(26, waveCount)};
  }
  return ripples;
}

float seaHit(vec3 eye, vec3 ray, float planeDepth, float clock, vec3 weights, float energy) {
  float geometryFade = 1.0 - smoothstep(14.0, 32.0, planeDepth);
  if (geometryFade <= 0.0 || weights.x <= 0.0) return planeDepth;

  // Start above the crest envelope and approach the displaced surface.
  // Damping keeps the correction stable on long, near-tangent rays.
  float envelope = energy * (0.38 * weights.x + 0.47 * weights.z);
  float range = envelope / max(0.03, -ray.y);
  float nearDepth = max(0.0, planeDepth - range);
  float farDepth = planeDepth + range;
  float depth = nearDepth;
  for (int i = 0; i < 8; i++) {
    vec3 point = eye + depth * ray;
    vec3 wave = energy * seaSwell(point.xz, clock, 0.0, weights);
    float error = point.y - wave.x;
    if (abs(error) < 0.007) break;
    float gradient = dot(wave.yz, ray.xz) - ray.y;
    float stepSize = clamp(error / max(0.24, gradient), -2.5, 2.5);
    depth = clamp(depth + 0.76 * stepSize, nearDepth, farDepth);
  }
  return mix(planeDepth, depth, geometryFade);
}

float seaGrid(vec2 position, float depth) {
  vec2 cell = abs(fract(position * vec2(0.48, 0.38) + 0.5) - 0.5);
  vec2 width = vec2(0.0015 + depth * 0.00044, 0.002 + depth * depth * 0.00017);
  vec2 line = 1.0 - smoothstep(width * 0.1, width, cell);
  float intensity = mix(0.31, 0.90, smoothstep(4.0, 27.0, depth));
  // Beyond this range the sub-pixel wireframe reads as a blue-gray strip.
  float unresolved = smoothstep(37.0, 83.0, depth);
  float mist = mix(0.21, 0.13, smoothstep(120.0, 900.0, depth));
  return mix(max(line.x, line.y) * intensity, mist, unresolved);
}

vec3 seaColor(vec3 eye, vec3 ray, vec3 sun, vec3 skyAtHorizon) {
  float clock = uClock * (0.55 + 0.28 * uWind);
  float single = smoothstep(0.0, 0.20, uWave);
  float complex = smoothstep(0.20, 0.97, uWave);
  vec3 weights = vec3(single, smoothstep(0.22, 0.84, uWave), complex);
  float morning = smoothstep(0.012, 0.145, sun.y);
  float energy = (0.65 + 0.41 * uWind) * mix(1.08, 0.72, morning);
  float planeDepth = eye.y / max(0.0015, -ray.y);
  float depth = seaHit(eye, ray, planeDepth, clock, weights, energy);
  vec2 position = (eye + depth * ray).xz;
  float footprint = depth * (0.00075 + 0.00037 * depth / max(eye.y, 1.0));
  vec3 ripples = vec3(0.0);
  if (complex > 0.0) {
    ripples = complex * (0.54 + 0.46 * uWind) * seaRipples(position, clock, footprint);
  }
  vec3 swell = energy * (seaSwell(position, clock, footprint, weights) + ripples);

  vec3 normal = normalize(vec3(-swell.y, 1.0, -swell.z));
  float facing = clamp(dot(-ray, normal), 0.0, 1.0);
  float fresnel = 0.022 + 0.978 * pow(1.0 - facing, 5.0);
  vec3 reflected = reflect(ray, normal);
  vec3 upward = normalize(vec3(reflected.x, max(0.004, reflected.y), reflected.z));
  float openSky = smoothstep(-0.15, 0.040, reflected.y);
  float aurora = 1.0 - smoothstep(0.0, 0.90, abs(uScene - 1.0));
  float eclipse = 1.0 - smoothstep(0.0, 0.90, abs(uScene - 2.0));
  float earlyDawn = (1.0 - aurora) * (1.0 - eclipse) * (1.0 - 0.70 * morning);
  vec2 alongSun = normalize(sun.xz);
  vec2 viewHeading = normalize(ray.xz);

  vec3 darkWater = mix(vec3(0.040, 0.022, 0.041), vec3(0.019, 0.038, 0.039), morning);
  darkWater = mix(darkWater, vec3(0.011, 0.058, 0.067), aurora);
  darkWater = mix(darkWater, vec3(0.023, 0.026, 0.055), eclipse);
  float swellLight = clamp(0.69 + 0.40 * swell.x + 0.44 * normal.z, 0.30, 1.0);
  vec3 reflectedColor = reflectedSky(upward, sun);
  float lowReflection = exp(-max(0.0, upward.y) * 18.0);
  vec3 waterTint = mix(vec3(1.0), vec3(0.60, 0.74, 1.14), earlyDawn);
  float mutedHorizon = 1.0 - earlyDawn * 0.46 * lowReflection;
  vec3 color = darkWater * swellLight
    + skyAtHorizon * (0.025 + 0.040 * swellLight) * (1.0 - 0.42 * earlyDawn);
  color += reflectedColor * waterTint * mutedHorizon
    * (0.12 + 0.63 * fresnel) * mix(0.46, 1.0, openSky);

  // Close wavelets modulate the light on the larger swell's faces.
  float rippleFace = smoothstep(-0.055, 0.080, energy * dot(ripples.yz, alongSun));
  float fineDetail = complex * (1.0 - smoothstep(9.0, 25.0, depth));
  color *= mix(1.0, mix(0.76, 1.10, rippleFace), fineDetail);
  color += vec3(0.091, 0.045, 0.055) * earlyDawn
    * fineDetail * openSky * pow(rippleFace, 2.6);

  // A narrow layer of marine haze joins the horizon without lifting all
  // of the wave faces in the middle distance to the sky's exposure.
  float mist = 1.0 - smoothstep(0.0, 0.012, -ray.y);
  color = mix(color, skyAtHorizon * 0.90, (0.76 - 0.28 * eclipse) * mist);

  // Reflection of the bright solar disc. The tighter lobes follow the
  // resolved facet normals, while the broad lobe retains sub-pixel glints.
  float sideways = dot(viewHeading, vec2(alongSun.y, -alongSun.x));
  float waterAngle = sqrt(max(0.0, -ray.y));
  float broadWidth = (0.018 + 0.099 * waterAngle) * (1.0 + 0.45 * morning + 0.50 * eclipse);
  float narrowWidth = 0.009 + 0.081 * waterAngle;
  float width = mix(broadWidth, narrowWidth, earlyDawn);
  float streak = exp(-pow(abs(sideways) / width, 2.0));
  streak *= smoothstep(0.38, 0.89, dot(viewHeading, alongSun));
  float angularError = max(0.0, 1.0 - dot(upward, sun));
  float warmScatter = exp(-31.0 * angularError);
  float glint = exp(-140.0 * angularError) * (0.41 + 0.36 * morning + 0.38 * eclipse)
    + exp(-710.0 * angularError) * 1.05 + exp(-3600.0 * angularError) * 1.62;
  float brokenPath = mix(0.48 + 0.52 * smoothstep(0.5, 0.86, swellLight),
    0.31 + 0.69 * smoothstep(0.59, 0.84, swellLight), earlyDawn);
  float directLight = (1.0 - aurora) * smoothstep(-0.023, 0.012, sun.y);
  float light = streak * directLight * (glint * brokenPath * mix(0.26, 1.0, openSky)
    + warmScatter * (0.08 + 0.16 * morning + 0.08 * eclipse) * (1.0 - 0.62 * earlyDawn));
  vec3 warmGlint = mix(vec3(1.0, 0.39, 0.12), vec3(1.0, 0.77, 0.43), max(morning, eclipse));
  vec3 glintColor = mix(warmGlint, vec3(1.0, 0.96, 0.79), smoothstep(0.32, 1.2, light));
  color += glintColor * (1.0 - exp(-light * (1.0 + 0.32 * earlyDawn)));

  if (uGrid > 0.0) {
    vec3 wireframe = vec3(0.005, 0.006, 0.009)
      + vec3(0.69, 0.75, 0.87) * seaGrid(position, depth);
    color = mix(color, wireframe, uGrid);
  }
  return color;
}
`;
