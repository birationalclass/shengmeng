export const oceanSource = `
const float OCEAN_PI = 3.14159265359;
const float OCEAN_WATER_IOR = 1.333;

float oceanRandom(vec2 p) {
  vec3 q = fract(vec3(p.xyx) * 0.1031);
  q += dot(q, q.yzx + 33.33);
  return fract((q.x + q.y) * q.z);
}

float oceanNoise(vec2 p) {
  vec2 cell = floor(p);
  vec2 f = fract(p);
  f = f * f * (3.0 - 2.0 * f);
  float a = oceanRandom(cell);
  float b = oceanRandom(cell + vec2(1.0, 0.0));
  float c = oceanRandom(cell + vec2(0.0, 1.0));
  float d = oceanRandom(cell + vec2(1.0, 1.0));
  return mix(mix(a, b, f.x), mix(c, d, f.x), f.y);
}

float oceanFbm(vec2 p) {
  const mat2 rotation = mat2(0.86, -0.51, 0.51, 0.86);
  float a = oceanNoise(p);
  p = rotation * p * 2.02 + 17.4;
  float b = oceanNoise(p);
  p = rotation * p * 2.05 + 7.8;
  return 0.57 * a + 0.29 * b + 0.14 * oceanNoise(p);
}

// The wavelength is in meters and the angular frequency follows deep-water dispersion.
vec2 oceanWave(vec2 p, vec2 direction, float wavelength, float steepness, float offset, float footprint, float time) {
  float k = 2.0 * OCEAN_PI / wavelength;
  float frequency = sqrt(9.81 * k);
  float phase = dot(p, direction) * k - time * frequency + offset;
  float resolvable = 1.0 - smoothstep(0.28, 0.66, footprint / wavelength);
  return direction * (steepness * cos(phase) * resolvable);
}

vec2 oceanSlopes(vec2 position, float footprint, float localWind, float time) {
  vec2 slopes = oceanWave(position, vec2(0.917, 0.398), 25.0, 0.041, 0.6, footprint, time);
  slopes += oceanWave(position, vec2(0.547, 0.837), 12.6, 0.052, 2.0, footprint, time);
  slopes += oceanWave(position, vec2(0.921, -0.389), 6.9, 0.055, 0.0, footprint, time);
  slopes += oceanWave(position, vec2(0.247, 0.969), 3.3, 0.051, 3.4, footprint, time);
  slopes += localWind * oceanWave(position, vec2(0.739, 0.673), 1.66, 0.058, 1.1, footprint, time);
  slopes += localWind * oceanWave(position, vec2(0.864, -0.503), 0.94, 0.048, 4.0, footprint, time);
  slopes += localWind * oceanWave(position, vec2(0.383, 0.924), 0.49, 0.050, 2.7, footprint, time);
  slopes += localWind * oceanWave(position, vec2(0.966, 0.259), 0.27, 0.044, 5.4, footprint, time);
  return slopes;
}

vec3 oceanReflectedClouds(vec3 atmosphere, vec2 world, vec3 reflected, vec3 sun, vec3 sunColor, float daylight, float time) {
  // One sample of a drifting cloud layer. The full sky cloud ray march stays in the sky pass.
  float distanceToLayer = min(32.0, 1.65 / max(reflected.y, 0.035));
  vec2 sampleAt = world + reflected.xz * distanceToLayer - vec2(0.0015, 0.004) * time;
  float cloud = smoothstep(0.55, 0.76, oceanFbm(sampleAt * 0.83 + vec2(-9.1, 4.3)));
  float backlit = pow(max(0.0, dot(reflected, sun)), 5.0);
  vec3 overcast = mix(vec3(0.18, 0.22, 0.27), vec3(0.56, 0.64, 0.72), daylight);
  overcast += sunColor * backlit * (0.28 + 0.16 * daylight);
  float grazingFade = smoothstep(0.015, 0.145, reflected.y);
  return mix(atmosphere, overcast, cloud * grazingFade * 0.48);
}

vec3 oceanColor(vec3 eye, vec3 ray, float hitDistance, vec3 sun, vec3 sunColor, vec3 atmosphereReflected, float cloudShade, float time, vec2 island) {
  float distanceKm = clamp(hitDistance, 0.0, 280.0);
  vec2 world = eye.xz + ray.xz * distanceKm;
  vec2 meters = world * 1000.0;
  float visibility = clamp(cloudShade, 0.0, 1.0);
  float daylight = smoothstep(-0.035, 0.39, sun.y);
  float sunset = 1.0 - smoothstep(0.07, 0.37, sun.y);
  float wind = mix(0.66, 1.32, oceanNoise(meters * 0.025 - vec2(0.08, 0.15) * time));

  // Estimate how much of the water plane one pixel sees at grazing angles.
  float footprint = max(0.075, distanceKm * 1.10 / max(abs(ray.y), 0.022));
  vec2 waveWarp = vec2(
    oceanNoise(meters * 0.048 + vec2(6.7, -11.8) - vec2(0.041, 0.073) * time),
    oceanNoise(meters * 0.039 + vec2(-8.3, 4.5) - vec2(0.050, 0.063) * time)
  ) - 0.5;
  vec2 slopes = oceanSlopes(meters + waveWarp * 4.6, footprint, wind, time);
  vec3 normal = normalize(vec3(-slopes.x, 1.0, -slopes.y));
  vec3 view = -ray;
  vec3 reflected = reflect(ray, normal);
  float incidence = clamp(dot(normal, view), 0.0, 1.0);
  float fresnel = 0.0204 + 0.9796 * pow(1.0 - incidence, 5.0);

  // The underwater shelf drops away offshore, with irregular turquoise sand banks and darker channels.
  float shelf = oceanFbm(world * 1.85 + vec2(16.2, -6.8));
  float shallow = (0.77 + 0.23 * smoothstep(0.25, 0.74, shelf))
    * max(0.62 * exp(-distanceKm * 1.4), exp(-length(world - island) * 7.9));
  float seabedDepth = mix(23.0, 1.35, shallow);
  seabedDepth += (0.5 - oceanNoise(world * 11.0 + 4.2)) * 3.15 * shallow;
  seabedDepth = max(seabedDepth, 1.05);
  vec3 transmitted = refract(ray, normal, 1.0 / OCEAN_WATER_IOR);
  float underwaterDistance = seabedDepth / max(-transmitted.y, 0.45);
  vec2 seabed = meters + underwaterDistance * transmitted.xz;
  float sand = oceanFbm(seabed * 0.077 + 2.7);
  vec3 bedColor = mix(vec3(0.039, 0.37, 0.27), vec3(0.13, 0.64, 0.43), smoothstep(0.30, 0.72, sand));

  // Thin, displaced ridges catch a little light on the nearest shallow bottom.
  float foldA = sin(dot(seabed, vec2(0.92, 0.49)) * 1.7 + slopes.x * 6.0 + time * 0.77);
  float foldB = sin(dot(seabed, vec2(-0.34, 0.93)) * 1.3 + slopes.y * 6.0 - time * 0.58);
  float caustic = pow(max(0.0, 1.0 - abs(foldA + foldB) * 1.22), 4.0);
  caustic *= exp(-0.33 * seabedDepth) * (1.0 - smoothstep(0.12, 0.54, footprint)) * visibility;
  bedColor += vec3(0.10, 0.18, 0.14) * caustic;

  vec3 absorption = exp(-underwaterDistance * vec3(0.40, 0.091, 0.062));
  vec3 openWater = mix(vec3(0.009, 0.105, 0.142), vec3(0.012, 0.29, 0.35), shallow);
  vec3 water = openWater * (1.0 - absorption) + bedColor * absorption;
  water *= mix(vec3(0.23, 0.33, 0.43), vec3(1.0), daylight);
  water *= mix(0.38, 1.0, visibility);

  vec3 reflection = oceanReflectedClouds(atmosphereReflected, world, reflected, sun, sunColor, daylight, time);
  float sunUp = smoothstep(-0.012, 0.027, sun.y);
  float bearing = dot(ray.xz, sun.xz) / max(0.001, length(ray.xz) * length(sun.xz));
  float sunsetPath = pow(max(0.0, bearing), 9.0) * sunset * sunUp;
  water = mix(water, water * vec3(0.88, 0.35, 0.12) + sunColor * visibility * 0.044, sunsetPath);
  reflection = mix(reflection, reflection * vec3(1.0, 0.78, 0.56), sunsetPath * 0.72);
  // Surface ripple orientations break up the sun path. The roughness increases as waves go subpixel.
  vec3 halfVector = normalize(sun + view + vec3(0.0, 0.00001, 0.0));
  float facingSun = max(dot(normal, sun), 0.0);
  float highlight = pow(max(0.0, dot(normal, halfVector)), mix(228.0, 76.0, smoothstep(0.12, 2.3, footprint)));
  float horizonSheen = pow(max(0.0, dot(reflect(ray, vec3(0.0, 1.0, 0.0)), sun)), 44.0);
  float glint = visibility * sunUp * (highlight * (0.23 + 0.77 * sqrt(facingSun)) * (1.65 + 4.6 * sunset) + horizonSheen * (0.045 + 0.35 * sunset));

  vec3 surface = mix(water, reflection, fresnel * 0.90);
  float horizon = smoothstep(3.0, 37.0, distanceKm);
  surface = mix(surface, atmosphereReflected, horizon * 0.88);
  return max(surface + sunColor * glint, vec3(0.0));
}
`;
