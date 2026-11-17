export const oceanSource = `
const float OCEAN_PI = 3.14159265359;
const float OCEAN_WATER_IOR = 1.333;

float oceanRandom(vec2 p) {
  vec3 q = fract(vec3(p.xyx) * 0.1031);
  q += dot(q, q.yzx + 33.33);
  return fract((q.x + q.y) * q.z);
}

vec3 oceanValueGradient(vec2 p) {
  vec2 cell = floor(p);
  vec2 f = fract(p);
  vec2 weight = f * f * (3.0 - 2.0 * f);
  vec2 derivative = 6.0 * f * (1.0 - f);
  float a = oceanRandom(cell);
  float b = oceanRandom(cell + vec2(1.0, 0.0));
  float c = oceanRandom(cell + vec2(0.0, 1.0));
  float d = oceanRandom(cell + vec2(1.0, 1.0));
  return vec3(
    mix(mix(a, b, weight.x), mix(c, d, weight.x), weight.y),
    derivative.x * mix(b - a, d - c, weight.y),
    derivative.y * mix(c - a, d - b, weight.x)
  );
}

float oceanNoise(vec2 p) {
  return oceanValueGradient(p).x;
}

float oceanFbm(vec2 p) {
  const mat2 rotation = mat2(0.86, -0.51, 0.51, 0.86);
  float a = oceanNoise(p);
  p = rotation * p * 2.02 + 17.4;
  float b = oceanNoise(p);
  p = rotation * p * 2.05 + 7.8;
  return 0.57 * a + 0.29 * b + 0.14 * oceanNoise(p);
}

// The swell uses deep-water dispersion. A spatially varying phase disperses the crests.
vec2 oceanSwellSlope(vec2 position, vec2 direction, float wavelength, float steepness, float footprint, float time) {
  float k = 2.0 * OCEAN_PI / wavelength;
  float packet = oceanNoise(position / (0.91 * wavelength) + direction * 12.8);
  float phase = dot(position, direction) * k - time * sqrt(9.81 * k) + (packet - 0.5) * 5.8;
  float crest = cos(phase) * (0.84 + 0.16 * sin(phase));
  return direction * steepness * crest * mix(0.55, 1.25, packet)
    * (1.0 - smoothstep(0.23, 0.58, footprint / wavelength));
}

vec2 oceanWindSlope(vec2 position, mat2 rotation, vec2 stretches, vec2 velocity, float footprint, float time) {
  vec2 positionInBand = rotation * (position - velocity * time) * stretches;
  vec2 gradient = oceanValueGradient(positionInBand).yz * stretches;
  float wavelength = 1.0 / max(stretches.x, stretches.y);
  return transpose(rotation) * gradient * (1.0 - smoothstep(0.28, 0.82, footprint / wavelength));
}

vec2 oceanSlopes(vec2 position, float footprint, float localWind, float time) {
  vec2 slope = oceanSwellSlope(position, vec2(0.81, 0.59), 18.7, 0.037, footprint, time);
  slope += oceanSwellSlope(position, vec2(-0.48, 0.88), 8.2, 0.045, footprint, time);
  slope += oceanSwellSlope(position, vec2(0.92, -0.39), 3.4, 0.053, footprint, time);
  vec2 windSlope = 0.21 * oceanWindSlope(position, mat2(0.81, -0.59, 0.59, 0.81),
    vec2(0.25, 0.51), vec2(0.38, 0.96), footprint, time);
  windSlope += 0.090 * oceanWindSlope(position + 17.0, mat2(0.36, 0.93, -0.93, 0.36),
    vec2(0.50, 1.28), vec2(-0.52, 0.64), footprint, time);
  windSlope += 0.039 * oceanWindSlope(position - 28.0, mat2(0.92, 0.39, -0.39, 0.92),
    vec2(1.31, 2.64), vec2(0.46, 0.14), footprint, time);
  return slope * (0.74 + 0.21 * localWind) + windSlope * localWind;
}

float oceanWeatherCover(vec2 position, bool high) {
  vec2 uv = cloudWeatherUV(position);
  float mask = high ? textureLod(uWeatherHi, uv, 0.0).r : textureLod(uWeatherLo, uv, 0.0).r;
  return cloudCover(mask, cloudWeatherEdge(uv));
}

vec3 oceanReflectedClouds(vec3 atmosphere, vec2 world, vec3 reflected, vec3 sun, vec3 sunColor, float daylight) {
  // Project only the existing low and high weather cover into the sea reflection.
  float zenith = max(0.052, reflected.y);
  vec2 lowPoint = world + reflected.xz * min(40.0, 2.15 / zenith);
  vec2 highPoint = world + reflected.xz * min(70.0, 6.3 / zenith);
  float lowMask = uLayers == 2 ? 0.0 : oceanWeatherCover(lowPoint, false);
  float highMask = uLayers == 1 ? 0.0 : oceanWeatherCover(highPoint, true);
  float lowBreakup = oceanFbm(lowPoint * 0.62 + vec2(-9.1, 4.3));
  float low = smoothstep(0.24, 0.87, lowMask + (lowBreakup - 0.48) * 0.48);
  float high = smoothstep(0.28, 0.82, highMask);
  float grazing = smoothstep(0.012, 0.15, reflected.y);
  float backlit = pow(max(0.0, dot(reflected, sun)), 5.0);
  vec3 overcast = mix(vec3(0.090, 0.103, 0.13), vec3(0.47, 0.54, 0.62), daylight);
  overcast += atmosphere * 0.15 + sunColor * backlit * (0.22 + 0.10 * daylight);
  return mix(atmosphere, overcast, (0.65 * low + 0.15 * high) * grazing);
}

vec3 oceanColor(vec3 eye, vec3 ray, float hitDistance, vec3 sun, vec3 sunColor, vec3 atmosphereReflected, float cloudShade, float time, vec2 island) {
  float distanceKm = clamp(hitDistance, 0.0, 280.0);
  vec2 world = eye.xz + ray.xz * distanceKm;
  vec2 meters = world * 1000.0;
  float visibility = clamp(cloudShade, 0.0, 1.0);
  float daylight = smoothstep(-0.035, 0.39, sun.y);
  float sunset = 1.0 - smoothstep(0.07, 0.37, sun.y);
  float gust = oceanFbm(meters * 0.026 - vec2(0.019, 0.012) * time);
  float wind = mix(0.48, 1.40, smoothstep(0.19, 0.83, gust));

  // Estimate how much of the water plane one pixel sees at grazing angles.
  float footprint = max(0.088, distanceKm * 1.23 / max(abs(ray.y), 0.019));
  vec2 waveWarp = vec2(
    oceanNoise(meters * 0.034 + vec2(6.7, -11.8) - vec2(0.031, 0.053) * time),
    oceanNoise(meters * 0.030 + vec2(-8.3, 4.5) - vec2(0.042, 0.065) * time)
  ) - 0.5;
  vec2 slopes = oceanSlopes(meters + waveWarp * 7.4, footprint, wind, time);
  vec3 normal = normalize(vec3(-slopes.x, 1.0, -slopes.y));
  vec3 view = -ray;
  vec3 reflected = reflect(ray, normal);
  float incidence = clamp(dot(normal, view), 0.0, 1.0);
  float fresnel = 0.0204 + 0.9796 * pow(1.0 - incidence, 5.0);

  // Mottled sand banks and dark channels follow the shallow reef around the island.
  float shelf = oceanFbm(meters * 0.018 + vec2(16.2, -6.8));
  float channel = oceanFbm(meters * 0.057 + shelf * 2.1);
  vec2 fromIsland = world - island;
  float islandRange = length(fromIsland);
  float coast = 1.0 - smoothstep(0.031, 0.077, islandRange + (shelf - 0.5) * 0.011);
  float nearShelf = exp(-distanceKm * 3.1) * smoothstep(0.23, 0.71, shelf);
  float shallow = max(coast, 0.64 * nearShelf);
  float seabedDepth = mix(27.0 + channel * 15.0, 0.85 + channel * 4.6, shallow);
  vec3 transmitted = refract(ray, normal, 1.0 / OCEAN_WATER_IOR);
  float underwaterDistance = seabedDepth / max(-transmitted.y, 0.45);
  vec2 seabed = meters + underwaterDistance * transmitted.xz;
  float sand = oceanFbm(seabed * 0.077 + 2.7);
  float sandCover = smoothstep(0.28, 0.74, sand + (channel - 0.5) * 0.33);
  vec3 bedColor = mix(vec3(0.024, 0.147, 0.143), vec3(0.22, 0.48, 0.31), sandCover);

  // Thin, displaced ridges catch a little light on the nearest shallow bottom.
  float foldA = sin(dot(seabed, vec2(0.92, 0.49)) * 1.7 + slopes.x * 6.0 + time * 0.77);
  float foldB = sin(dot(seabed, vec2(-0.34, 0.93)) * 1.3 + slopes.y * 6.0 - time * 0.58);
  float caustic = pow(max(0.0, 1.0 - abs(foldA + foldB) * 1.22), 4.0);
  caustic *= exp(-0.33 * seabedDepth) * (1.0 - smoothstep(0.12, 0.54, footprint)) * visibility;
  bedColor += vec3(0.10, 0.18, 0.14) * caustic;

  vec3 absorption = exp(-underwaterDistance * vec3(0.46, 0.104, 0.065));
  float lagoonLight = clamp(shallow * (0.57 + 0.38 * sandCover), 0.0, 1.0);
  vec3 openWater = mix(vec3(0.008, 0.075, 0.125), vec3(0.009, 0.252, 0.255), lagoonLight);
  vec3 water = openWater * (1.0 - absorption) + bedColor * absorption;
  water *= mix(vec3(0.23, 0.33, 0.43), vec3(1.0), daylight);
  water *= mix(0.38, 1.0, visibility);

  vec3 reflection = oceanReflectedClouds(atmosphereReflected, world, reflected, sun, sunColor, daylight);
  if (islandRange < 0.14) {
    // A rough-water reflection anchors the silhouette to the sheltered coast.
    vec2 tangent = reflected.xz;
    float t = -dot(fromIsland, tangent) / max(dot(tangent, tangent), 0.001);
    float reflectedRange = length(fromIsland + tangent * max(t, 0.0));
    float reflectedHeight = reflected.y * max(t, 0.0);
    float rockMirror = smoothstep(0.0, 0.013, t) * (1.0 - smoothstep(0.020, 0.043, reflectedRange));
    rockMirror *= (1.0 - smoothstep(0.008, 0.024, reflectedHeight))
      * smoothstep(-0.001, 0.002, reflectedHeight);
    vec3 ledge = mix(vec3(0.024, 0.024, 0.023), vec3(0.098, 0.092, 0.075), daylight * visibility);
    reflection = mix(reflection, ledge, rockMirror * mix(0.58, 0.86, gust));

    float shoreBreak = smoothstep(0.04, 0.73, coast) * (1.0 - smoothstep(0.77, 1.0, coast));
    float foam = smoothstep(0.69, 0.85, oceanNoise(meters * 0.18 + slopes * 3.0 - time * 0.08));
    float shoreLight = shoreBreak * foam * (0.14 + 0.20 * daylight) * visibility;
    water += vec3(0.39, 0.55, 0.51) * shoreLight;
  }
  float sunUp = smoothstep(-0.012, 0.027, sun.y);
  float bearing = dot(ray.xz, sun.xz) / max(0.001, length(ray.xz) * length(sun.xz));
  float sunsetPath = pow(max(0.0, bearing), 9.0) * sunset * sunUp;
  water = mix(water, water * vec3(0.88, 0.35, 0.12) + sunColor * visibility * 0.044, sunsetPath);
  reflection = mix(reflection, reflection * vec3(1.0, 0.78, 0.56), sunsetPath * 0.72);
  // Surface ripple orientations break up the sun path. The roughness increases as waves go subpixel.
  vec3 halfVector = normalize(sun + view + vec3(0.0, 0.00001, 0.0));
  float facingSun = max(dot(normal, sun), 0.0);
  float highlight = pow(max(0.0, dot(normal, halfVector)), mix(168.0, 61.0, smoothstep(0.12, 2.6, footprint)));
  float horizonSheen = pow(max(0.0, dot(reflect(ray, vec3(0.0, 1.0, 0.0)), sun)), 54.0);
  float glint = visibility * sunUp * (highlight * (0.23 + 0.77 * sqrt(facingSun)) * (1.65 + 4.6 * sunset) + horizonSheen * (0.045 + 0.35 * sunset));

  vec3 surface = mix(water, reflection, fresnel * 0.90);
  float horizon = smoothstep(3.0, 37.0, distanceKm);
  surface = mix(surface, atmosphereReflected, horizon * 0.90);
  return max(surface + sunColor * glint, vec3(0.0));
}
`;
