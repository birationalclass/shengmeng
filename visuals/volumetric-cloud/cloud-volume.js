// Browser implementation of the authored Lo/Hi weather-map model and the
// directional / isotropic light paths described by AshenOneArt (HanPi).
// https://github.com/AshenOneArt/HPVolumeCloud
// Density profiles and edge erosion follow the approach in Guerrilla's Nubis.
// https://www.guerrilla-games.com/read/nubis-realtime-volumetric-cloudscapes-in-a-nutshell
export const cloudSource = `
uniform sampler2D uWeatherLo, uWeatherHi;
uniform highp sampler3D uShape, uDetail;
uniform highp sampler3D uReferenceCloud;
uniform vec3 uReferenceCenter, uReferenceSize;
uniform float uReferenceHeading;
uniform bool uUseReference;
uniform float uWeatherSpan, uWindTime, uCoverage, uThickness, uDiffusion;
uniform int uCloudSteps, uLightSteps, uDebugCloud, uLayers;
uniform vec3 uSunColor;

const float cloudEarthRadius = 6371.0;
const vec2 cloudWindVelocity = vec2(0.023, -0.012);
const float cloudBase = 1.13;
const float cloudBottomLimit = 0.10;
const float cloudTopLimit = 20.0;

float cloudAltitude(vec3 p) {
  // Compensated altitude to avoid subtracting nearly equal Earth-size values.
  float r = cloudEarthRadius + p.y;
  return p.y + dot(p.xz, p.xz) / (sqrt(r * r + dot(p.xz, p.xz)) + r);
}

vec2 cloudWeatherUV(vec2 world) {
  return 0.5 + (world - cloudWindVelocity * uWindTime) / max(1.0, uWeatherSpan);
}

float cloudWeatherEdge(vec2 uv) {
  float edge = min(min(uv.x, 1.0 - uv.x), min(uv.y, 1.0 - uv.y));
  return smoothstep(0.0, 0.045, edge);
}

float cloudCover(float mask, float edge) {
  return clamp(pow(mask, 1.12) * uCoverage * edge, 0.0, 1.0);
}

vec3 cloudTypes(float type) {
  float congestus = 1.0 - abs(2.0 * type - 1.0);
  return vec3(1.0 - smoothstep(0.0, 0.5, type), congestus,
    smoothstep(0.5, 1.0, type));
}

float cloudLowBase(vec4 weather) {
  float measuredTop = weather.a * 18.0;
  if (weather.a <= 0.001) return cloudBase;
  // A marine cloud with a retrieved top below 1 km cannot share the base of a
  // deep convective column. The base here is inferred, the top is observed.
  return clamp(0.47 * measuredTop + 0.035, cloudBottomLimit, cloudBase);
}

float cloudLowHeight(vec4 weather) {
  float coverageHeight = pow(weather.r, 0.82);
  float stratus = clamp(weather.b, 0.0, 1.0);
  float height = mix(1.9, 5.15, pow(weather.g, 1.26)) * (0.67 + 0.58 * coverageHeight);
  height = mix(height, 0.84 + 0.84 * coverageHeight, stratus);
  if (weather.a > 0.001) height = max(0.075, 18.0 * weather.a - cloudLowBase(weather));
  return height * uThickness;
}

float cloudRemap(float field, float floorValue) {
  return clamp((field - floorValue) / max(0.001, 1.0 - floorValue), 0.0, 1.0);
}

float cloudErode(float body, vec3 detailUV, float strength, bool detail) {
  float porosity = 0.45;
  if (detail) {
    vec3 detailField = textureLod(uDetail, detailUV, 0.0).rgb;
    porosity = 1.0 - dot(detailField, vec3(0.58, 0.29, 0.13));
  }
  // Only the shell has much exposure to dry air. Preserve the dense core.
  float envelope = 1.0 - smoothstep(0.15, 0.68, body);
  return cloudRemap(body, porosity * strength * envelope);
}

float cloudLowDensity(vec3 p, float altitude, vec4 weather, float coverage, bool detail) {
  if (coverage < 0.055) return 0.0;
  float base = cloudLowBase(weather);
  float roof = cloudLowHeight(weather);
  if (roof <= 0.0) return 0.0;
  if (altitude <= base - 0.022 || altitude >= base + roof * 1.20) return 0.0;
  float localHeight = (altitude - base) / max(0.075, roof);
  float shallowDeck = (1.0 - smoothstep(0.38, 1.25, roof)) * smoothstep(0.42, 0.88, coverage);
  float stratus = max(weather.b, 0.54 * shallowDeck);
  vec3 types = cloudTypes(weather.g);
  types /= dot(types, vec3(1.0));
  vec2 drift = cloudWindVelocity * uWindTime;
  vec2 ground = p.xz - drift;
  vec3 broadUV = vec3(ground.x * 0.069, 0.43 + 0.052 * altitude, ground.y * 0.069);
  vec4 broad = textureLod(uShape, broadUV, 0.0);
  float cellRise = smoothstep(0.23, 0.79, broad.g);
  float convectiveCap = mix(0.73, 1.15, broad.r);
  float stratiformCap = mix(0.58, 1.12, cellRise);
  float ceiling = mix(convectiveCap, stratiformCap, stratus);
  float baseDrift = (broad.b - 0.5) * mix(0.095, 0.028, stratus) * min(1.0, 0.42 / roof);
  float h = (localHeight - baseDrift) / ceiling;
  if (h <= 0.0 || h >= 1.0) return 0.0;

  // Higher thermals lean with altitude. Normalizing part of the Y coordinate
  // resolves rounded 3D lobes even through a shallow marine deck.
  vec2 lean = vec2(0.21, -0.15) * roof * h * h * (0.3 + 0.7 * weather.g);
  vec2 sampleXZ = (ground + lean) * mix(0.157, 0.142, stratus)
    + 0.18 * (broad.ba - 0.5);
  vec3 bodyUV = vec3(sampleXZ.x, altitude * 0.13 + h * mix(0.29, 0.155, stratus), sampleXZ.y);
  vec3 volume = textureLod(uShape, bodyUV, 0.0).rgb;

  // Cumulus has a compact lower core and separated crowns. Congestus and
  // deep clouds retain a full column and can broaden slightly near the top.
  float crown = dot(types, vec3(0.39, 0.51, 0.61));
  float convexity = smoothstep(crown, 1.0, h);
  float anvil = types.z * smoothstep(0.58, 0.86, h) * (1.0 - smoothstep(0.84, 1.0, h));
  float hull = mix(volume.r, max(volume.r, 0.86 * volume.g), 0.43);
  hull = mix(hull, 0.50 * volume.r + 0.32 * broad.r + 0.18 * volume.g, 0.55 * stratus);
  float baseLip = 1.0 - smoothstep(0.06, 0.19, h);
  float moistBase = mix(0.012, 0.049, stratus) * baseLip * coverage;
  float opening = mix(0.76, 0.295, pow(coverage, 1.42)) - 0.093 * (broad.r - 0.5);
  opening += convexity * mix(0.26, 0.20, stratus) - 0.09 * anvil;
  opening += stratus * 0.20 * (1.0 - cellRise);
  float body = cloudRemap(hull + moistBase, opening);
  if (body <= 0.0) return 0.0;

  vec3 ruffleUV = bodyUV * vec3(3.32, 2.91, 3.32) + vec3(0.27, 0.56, 0.18);
  ruffleUV.xz -= drift * 0.11;
  ruffleUV += (vec3(broad.g, volume.b, volume.g) - 0.5) * 0.24;
  float edgeStrength = mix(0.24, 0.34, stratus) * (0.72 + 0.28 * smoothstep(0.08, 0.36, h));
  body = cloudErode(body, ruffleUV, edgeStrength, detail);
  float baseMask = smoothstep(0.0, mix(0.13, 0.072, stratus), h);
  float crownMask = 1.0 - smoothstep(mix(0.69, 0.83, stratus), 1.0, h);
  float taper = baseMask * crownMask;
  float denseCore = body * taper * smoothstep(0.0, 0.13, body);
  return denseCore * mix(6.4, 7.65, weather.g) * mix(0.94, 1.10, shallowDeck);
}

float cloudHighDensity(vec3 p, float altitude, vec4 weather, float coverage, bool detail) {
  if (coverage < 0.065) return 0.0;
  float measuredTop = weather.b * 18.0;
  float base = 6.15 - 0.4 * coverage;
  float ceiling = 0.26 + 2.7 * pow(coverage, 1.45);
  float cellular = smoothstep(0.24, 0.83, weather.g);
  if (weather.b > 0.001) {
    base = clamp(measuredTop - mix(1.55, 2.75, cellular), 3.2, 15.8);
    ceiling = max(0.24, measuredTop - base);
  }
  ceiling *= sqrt(max(0.2, uThickness));
  if (altitude < base - 0.09 || altitude >= base + 1.18 * ceiling) return 0.0;

  vec2 windPosition = p.xz - cloudWindVelocity * (uWindTime * 1.27);
  vec2 ground = vec2(dot(vec2(0.913, 0.408), windPosition),
    dot(vec2(-0.408, 0.913), windPosition));
  vec4 broad = textureLod(uShape, vec3(0.045 * ground.x, 0.063 * base, 0.059 * ground.y), 0.0);
  float clusters = smoothstep(0.21, 0.81, broad.g);
  float depth = ceiling * mix(0.79 + 0.24 * broad.r, 0.60 + 0.53 * clusters, cellular);
  float h = (altitude - base - 0.13 * (broad.b - 0.5)) / max(0.16, depth);
  if (h <= 0.0 || h >= 1.0) return 0.0;

  // Altostratus stretches modestly into sheets. Altocumulus has rounded cells
  // at each altitude. Neither is a single, vertically invariant texture slice.
  vec2 sampleXZ = ground * mix(vec2(0.088, 0.126), vec2(0.141), cellular);
  sampleXZ += (broad.ab - 0.5) * 0.24;
  vec3 highUV = vec3(sampleXZ.x, altitude * 0.079 + h * mix(0.093, 0.21, cellular), sampleXZ.y);
  vec3 volume = textureLod(uShape, highUV, 0.0).rgb;
  float opening = mix(0.72, 0.32, pow(coverage, 1.24)) + 0.09 * cellular * (1.0 - clusters);
  opening += smoothstep(0.55, 1.0, h) * mix(0.24, 0.34, cellular);
  float body = cloudRemap(mix(volume.r, max(volume.r, volume.g * 0.88), 0.61 * cellular), opening);
  if (body <= 0.0) return 0.0;

  vec3 detailUV = highUV * vec3(2.55, 2.81, 2.83) + vec3(0.47, 0.12, 0.36);
  body = cloudErode(body, detailUV, mix(0.22, 0.34, cellular), detail);
  float rim = smoothstep(0.0, 0.16, h) * (1.0 - smoothstep(0.64, 1.0, h));
  return pow(body, mix(0.93, 0.74, cellular)) * rim
    * mix(0.88, 1.45, weather.a) * mix(0.80, 2.25, cellular);
}

vec3 referenceLocal(vec3 p) {
  float c = cos(uReferenceHeading), s = sin(uReferenceHeading);
  return vec3(c * p.x - s * p.z, p.y, s * p.x + c * p.z);
}

float referenceDensity(vec3 p) {
  vec3 delta = p - uReferenceCenter;
  delta.xz -= cloudWindVelocity * uWindTime * 0.24;
  vec3 uv = referenceLocal(delta) / uReferenceSize + 0.5;
  if (any(lessThanEqual(uv, vec3(0.0))) || any(greaterThanEqual(uv, vec3(1.0)))) return 0.0;
  // The library supplies the complete 3D extinction field. Interpolate the
  // production voxels without running the weather-map erosion on them again.
  return textureLod(uReferenceCloud, uv, 0.0).r * 17.0;
}

float cloudDensity(vec3 p, bool detail) {
  if (uUseReference) return referenceDensity(p);
  float altitude = cloudAltitude(p);
  if (altitude <= cloudBottomLimit || altitude > cloudTopLimit) return 0.0;
  vec2 uv = cloudWeatherUV(p.xz);
  float edge = cloudWeatherEdge(uv);
  if (edge <= 0.0) return 0.0;

  float result = 0.0;
  if (uLayers != 2) {
    vec4 lo = textureLod(uWeatherLo, uv, 0.0);
    result = cloudLowDensity(p, altitude, lo, cloudCover(lo.r, edge), detail);
  }
  if (uLayers != 1 && altitude > 3.2) {
    vec4 hi = textureLod(uWeatherHi, uv, 0.0);
    result += cloudHighDensity(p, altitude, hi, cloudCover(hi.r, edge), detail);
  }
  return result;
}

float cloudWeatherTop(vec2 uv) {
  vec4 lo = textureLod(uWeatherLo, uv, 0.0);
  return (cloudLowBase(lo) + cloudLowHeight(lo)) * smoothstep(0.025, 0.30, lo.r)
    * cloudWeatherEdge(uv);
}

float cloudBoundaryConfidence(vec3 p, vec3 sun) {
  if (uUseReference) {
    float center = referenceDensity(p);
    float upwind = referenceDensity(p + 0.24 * sun);
    return clamp(0.67 + 0.25 * (center - upwind), 0.20, 1.0);
  }
  if (uLayers == 2) return 0.72;
  vec2 uv = cloudWeatherUV(p.xz);
  vec2 delta = vec2(0.58 / max(1.0, uWeatherSpan), 0.0);
  float gradientX = cloudWeatherTop(uv + delta) - cloudWeatherTop(uv - delta);
  float gradientZ = cloudWeatherTop(uv + delta.yx) - cloudWeatherTop(uv - delta.yx);
  vec3 topNormal = normalize(vec3(-gradientX, 1.16, -gradientZ));
  float facing = clamp(0.43 + 0.79 * dot(topNormal, sun), 0.0, 1.0);
  return mix(facing, 0.72, smoothstep(5.5, 7.3, cloudAltitude(p)));
}

float cloudHg(float cosine, float g) {
  float q = (1.0 - g) * (1.0 - g) + 2.0 * g * (1.0 - cosine);
  return (1.0 - g * g) * inversesqrt(q) / q;
}

// Jendersie & d'Eon (SIGGRAPH 2023), approximate Mie for a 20 μm droplet.
// The forward lobe is averaged over the finite sun disc at this pixel scale.
float cloudMie(float cosine) {
  float mu = min(cosine, 0.99955);
  const float g = 0.5567;
  const float alpha = 21.9955;
  float draine = cloudHg(mu, g) * (1.0 + alpha * mu * mu)
    / (1.0 + alpha * (1.0 + 2.0 * g * g) / 3.0);
  return min(6.2, mix(cloudHg(mu, 0.9881), draine, 0.4824));
}

vec3 cloudLight(vec3 p, vec3 sun, bool withDiffusion, float boundary, float localDensity) {
  float distance = 0.27;
  int lightSteps = clamp(uLightSteps, 2, 8);
  float cloudPath = mix(17.0, 6.7, smoothstep(0.0, 0.8, sun.y));
  float interval = cloudPath * 0.81 / (pow(1.81, float(lightSteps)) - 1.0);
  // Resolve the nearby erosion lobes before widening the solar integration.
  float directDepth = cloudDensity(p + sun * 0.048, true) * 0.095
    + cloudDensity(p + sun * 0.17, true) * 0.175;
  float isotropic = withDiffusion ? 1.0 - exp(-0.57 * directDepth) : 0.0;
  for (int j = 0; j < 8; ++j) {
    if (j >= lightSteps) break;
    float sampleDistance = distance + interval * 0.48;
    float section = cloudDensity(p + sun * sampleDistance, j == 0) * interval;
    if (withDiffusion) {
      // One-dimensional Green kernel with slower attenuation than ballistic
      // transport. Deposited energy near edges feeds the built-up cloud field.
      float transport = exp(-0.115 * sampleDistance - 0.15 * directDepth);
      isotropic += transport * (1.0 - exp(-0.57 * section)) / (1.0 + 0.22 * distance);
    }
    directDepth += section;
    distance += interval;
    interval *= 1.81;
    if (directDepth > 16.0 && !withDiffusion) break;
  }
  float build = 1.0 - exp(-0.77 * directDepth);
  // Skylight arriving from above is also attenuated by the overlying volume.
  vec3 up = normalize(vec3(p.x, cloudEarthRadius + p.y, p.z));
  float upDepth = 0.055 * localDensity
    + 0.15 * cloudDensity(p + up * 0.13, true)
    + 0.34 * cloudDensity(p + up * 0.38, false)
    + 0.91 * cloudDensity(p + up * 1.04, false);
  return vec3(directDepth, (1.0 - exp(-0.88 * isotropic)) * build * boundary, upDepth);
}

vec2 cloudSphereRay(vec3 eye, vec3 ray, float altitude) {
  float b = dot(eye, ray) + cloudEarthRadius * ray.y;
  float c = dot(eye.xz, eye.xz) + (eye.y - altitude) * (2.0 * cloudEarthRadius + eye.y + altitude);
  float discriminant = b * b - c;
  if (discriminant <= 0.0) return vec2(1.0e7, -1.0e7);
  float q = -b - (b >= 0.0 ? 1.0 : -1.0) * sqrt(discriminant);
  float other = c / q;
  return vec2(min(q, other), max(q, other));
}

vec2 cloudShellRay(vec3 eye, vec3 ray, float base, float top, float limit) {
  vec2 outer = cloudSphereRay(eye, ray, top);
  vec2 inner = cloudSphereRay(eye, ray, base);
  vec2 range = vec2(max(0.0, outer.x), min(limit, outer.y));
  if (inner.x <= range.x && inner.y > range.x) range.x = inner.y;
  return range.y > range.x ? range : vec2(1.0e7, -1.0e7);
}

vec2 referenceInterval(vec3 eye, vec3 ray, float limit) {
  vec3 offset = eye - uReferenceCenter;
  offset.xz -= cloudWindVelocity * uWindTime * 0.24;
  vec3 start = referenceLocal(offset);
  vec3 direction = referenceLocal(ray);
  vec3 safe = max(vec3(0.00001), abs(direction)) * mix(vec3(-1), vec3(1), step(vec3(0.0), direction));
  vec3 a = (-0.5 * uReferenceSize - start) / safe;
  vec3 b = (0.5 * uReferenceSize - start) / safe;
  vec3 enter = min(a, b);
  vec3 exit = max(a, b);
  float near = max(0.0, max(enter.x, max(enter.y, enter.z)));
  float far = min(limit, min(exit.x, min(exit.y, exit.z)));
  return vec2(near, far);
}

// Low-cloud projected occlusion for the surface and islands.
float cloudShadow(vec3 p, vec3 sun) {
  if (sun.y <= 0.015) return 1.0;
  if (uUseReference) {
    vec2 interval = referenceInterval(p, sun, 45.0);
    if (interval.x >= interval.y) return 1.0;
    float stepSize = (interval.y - interval.x) / 7.0;
    float total = 0.0;
    for (int i = 0; i < 7; i++) {
      total += referenceDensity(p + sun * (interval.x + (float(i) + 0.5) * stepSize)) * stepSize;
    }
    return 0.18 + 0.82 * exp(-total);
  }
  float altitude = cloudAltitude(p);
  float zenith = max(0.04, sun.y);
  float lowCover = 0.0;
  float highCover = 0.0;
  if (uLayers != 2) {
    vec2 uv = cloudWeatherUV(p.xz + sun.xz * (max(0.0, 2.2 - altitude) / zenith));
    lowCover = cloudCover(textureLod(uWeatherLo, uv, 0.0).r, cloudWeatherEdge(uv));
  }
  if (uLayers != 1) {
    vec2 uv = cloudWeatherUV(p.xz + sun.xz * (max(0.0, 6.8 - altitude) / zenith));
    highCover = cloudCover(textureLod(uWeatherHi, uv, 0.0).r, cloudWeatherEdge(uv));
  }
  return exp(-1.26 * smoothstep(0.22, 0.95, lowCover) - 0.26 * highCover);
}

// Color is premultiplied scene-linear radiance. Distance is the optical
// contribution centroid along the ray (maxDistance for a transparent pixel).
vec4 marchCloud(vec3 eye, vec3 ray, vec3 sun, float maxDistance, float jitter, out float cloudDistance) {
  cloudDistance = maxDistance;
  if (uCoverage < 0.001 || maxDistance <= 0.08) return vec4(0.0);
  float limit = min(maxDistance, uWeatherSpan * 0.70);
  float lowTop = min(cloudTopLimit, cloudBase + 21.24 * uThickness);
  vec2 noHit = vec2(1.0e7, -1.0e7);
  vec2 low = uLayers == 2 ? noHit : cloudShellRay(eye, ray, cloudBottomLimit, lowTop, limit);
  vec2 high = uLayers == 1 ? noHit : cloudShellRay(eye, ray, 3.2, cloudTopLimit, limit);
  if (uUseReference) {
    low = referenceInterval(eye, ray, limit);
    high = noHit;
  }
  float start = min(low.x, high.x);
  float end = max(low.y, high.y);
  if (start >= end) return vec4(0.0);

  int steps = clamp(uCloudSteps, 12, 144);
  float span = end - start;
  float baseStep = max(0.072, span / float(steps));
  float cosTheta = clamp(dot(ray, sun), -1.0, 1.0);
  float phase = 0.74 * cloudMie(cosTheta);
  float secondOrder = 0.105 + 0.185 * cloudHg(cosTheta, 0.48);
  float thirdOrder = 0.115 + 0.064 * cloudHg(cosTheta, 0.23);
  float day = smoothstep(-0.09, 0.39, sun.y);
  float sunVisible = smoothstep(-0.115, 0.045, sun.y);
  bool withDiffusion = uDiffusion > 0.001 && uDebugCloud != 2;
  float sampleFraction = 0.30 + 0.40 * clamp(jitter, 0.0, 1.0);
  float transmittance = 1.0;
  vec3 radiance = vec3(0.0);
  float weightedDistance = 0.0;
  float t = start;
  float skipped = 0.0;

  for (int i = 0; i < 144; ++i) {
    if (i >= steps || t >= end || transmittance < 0.0035) break;
    bool inLow = t >= low.x && t < low.y;
    bool inHigh = t >= high.x && t < high.y;
    if (!inLow && !inHigh) {
      t = min(t < low.x ? low.x : 1.0e7, t < high.x ? high.x : 1.0e7);
      skipped = 0.0;
      continue;
    }
    float layerEnd = max(inLow ? low.y : -1.0, inHigh ? high.y : -1.0);
    float travel = clamp((t - start) / span, 0.0, 1.0);
    float distanceStep = max(0.036, (0.065 + t * 0.026) * 87.0 / float(steps));
    float stepSize = min(layerEnd - t, min(distanceStep, baseStep * (0.81 + 0.79 * travel)));
    if (uUseReference) stepSize = min(layerEnd - t, max(0.020, span / float(steps) * 1.35));
    float sampleDistance = t + sampleFraction * stepSize;
    vec3 p = eye + ray * sampleDistance;
    float rho = cloudDensity(p, true);
    if (rho < 0.004) {
      skipped = min(layerEnd - t, uUseReference ? 1.85 * stepSize
        : max(stepSize * 2.14, min(2.4, 0.15 + 0.041 * t)));
      t += skipped;
      continue;
    }
    if (skipped > stepSize) {
      // Refine the appearance of the first lit face after an empty-space jump.
      t -= 0.56 * (skipped - stepSize);
      sampleDistance = t + sampleFraction * stepSize;
      p = eye + ray * sampleDistance;
      rho = cloudDensity(p, true);
    }
    skipped = 0.0;
    float opacity = 1.0 - exp(-rho * stepSize);
    float contributing = transmittance * opacity;
    if (uDebugCloud == 4 && contributing > 0.0003) {
      if (uUseReference) {
        radiance += contributing * mix(vec3(0.25, 0.60, 0.90), vec3(0.98, 0.61, 0.21),
          smoothstep(0.4, 6.5, rho));
      } else {
      vec2 uv = cloudWeatherUV(p.xz);
      float altitude = cloudAltitude(p);
      float edge = cloudWeatherEdge(uv);
      vec4 lw = textureLod(uWeatherLo, uv, 0.0);
      vec4 hw = textureLod(uWeatherHi, uv, 0.0);
      float lowContribution = uLayers == 2 ? 0.0 : cloudLowDensity(p, altitude, lw, cloudCover(lw.r, edge), false);
      float highContribution = uLayers == 1 ? 0.0 : cloudHighDensity(p, altitude, hw, cloudCover(hw.r, edge), false);
      vec3 lowColor = mix(vec3(0.18, 0.66, 0.81), vec3(0.95, 0.56, 0.19), lw.g);
      lowColor = mix(lowColor, vec3(0.32, 0.78, 0.38), lw.b * 0.8);
      vec3 highColor = mix(vec3(0.37, 0.29, 0.85), vec3(0.82, 0.48, 0.86), hw.g);
      radiance += contributing * mix(lowColor, highColor, highContribution / max(0.001, lowContribution + highContribution));
      }
    } else if (uDebugCloud != 1 && contributing > 0.0003) {
      float boundary = withDiffusion ? cloudBoundaryConfidence(p, sun) : 0.0;
      vec3 optical = cloudLight(p, sun, withDiffusion, boundary, rho);
      float shadow = exp(-optical.x);
      float skyOcclusion = exp(-0.79 * optical.z);
      float altitude = cloudAltitude(p);
      float upperLight = smoothstep(0.9, 4.5, altitude);
      vec3 ambient = mix(vec3(0.012, 0.014, 0.028), vec3(0.22, 0.32, 0.47), day)
        * (0.16 + 0.87 * skyOcclusion) * mix(0.81, 1.18, upperLight);
      ambient += mix(vec3(0.007, 0.006, 0.004), vec3(0.033, 0.057, 0.060), day)
        * exp(-0.14 * max(0.0, altitude)) * (0.50 + 0.50 * skyOcclusion);
      vec3 highSun = mix(uSunColor, max(uSunColor, vec3(uSunColor.r * 0.88)),
        (1.0 - day) * smoothstep(0.8, 8.0, altitude) * 0.39);
      vec3 direct = highSun * sunVisible * (phase * shadow
        + 0.71 * secondOrder * exp(-0.39 * optical.x) + 0.63 * thirdOrder * exp(-0.14 * optical.x));
      float thickGate = smoothstep(0.065, 0.42, rho);
      vec3 diffuse = highSun * (0.31 * sunVisible * uDiffusion * optical.y * thickGate);
      vec3 light = ambient + direct + diffuse;
      if (uDebugCloud == 2) light = direct;
      if (uDebugCloud == 3) light = diffuse;
      radiance += contributing * light;
    }
    weightedDistance += sampleDistance * contributing;
    transmittance *= 1.0 - opacity;
    t += stepSize;
  }
  float alpha = 1.0 - transmittance;
  if (alpha > 0.0001) cloudDistance = weightedDistance / alpha;
  if (uDebugCloud == 1) radiance = vec3(0.20 + 0.80 * alpha) * alpha;
  return vec4(radiance, alpha);
}
`;
