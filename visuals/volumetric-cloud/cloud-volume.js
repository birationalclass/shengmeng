// Browser implementation of the authored Lo/Hi weather-map model and the
// directional / isotropic light paths described by AshenOneArt (HanPi).
// https://github.com/AshenOneArt/HPVolumeCloud
export const cloudSource = `
uniform sampler2D uWeatherLo, uWeatherHi;
uniform highp sampler3D uShape, uDetail;
uniform float uWeatherSpan, uWindTime, uCoverage, uThickness, uDiffusion;
uniform int uCloudSteps, uLightSteps, uDebugCloud, uLayers;
uniform vec3 uSunColor;

const float cloudEarthRadius = 6371.0;
const vec2 cloudWindVelocity = vec2(0.023, -0.012);
const float cloudBase = 1.13;
const float cloudBottomLimit = 0.27;
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
  return clamp(measuredTop - 0.48, cloudBottomLimit, cloudBase);
}

float cloudLowHeight(vec4 weather) {
  float coverageHeight = pow(weather.r, 0.82);
  float stratus = clamp(weather.b, 0.0, 1.0);
  float height = mix(1.9, 5.15, pow(weather.g, 1.26)) * (0.67 + 0.58 * coverageHeight);
  height = mix(height, 0.84 + 0.84 * coverageHeight, stratus);
  if (weather.a > 0.001) height = max(0.32, 18.0 * weather.a - cloudLowBase(weather));
  return height * uThickness;
}

float cloudProfile(float h, float bottom, float firstShoulder, float secondShoulder) {
  return smoothstep(0.0, bottom, h) * (1.0 - smoothstep(firstShoulder, secondShoulder, h));
}

float cloudLowDensity(vec3 p, float altitude, vec4 weather, float coverage, bool detail) {
  if (coverage < 0.015) return 0.0;
  float base = cloudLowBase(weather);
  float roof = cloudLowHeight(weather);
  if (altitude <= base || altitude >= base + roof * 1.18) return 0.0;
  float stratus = weather.b;
  vec3 bodyUV = vec3(p.x, altitude, p.z) * vec3(0.113, 0.142, 0.113);
  bodyUV.xz -= cloudWindVelocity * (uWindTime * 0.127);
  // Wind shear tilts tall towers. The base stays attached to its weather cell.
  bodyUV.xz += (altitude - base) * vec2(0.047, -0.029) * weather.g;
  vec3 volume = textureLod(uShape, bodyUV, 0.0).rgb;
  float layerHeight = roof * mix(1.0, 0.54 + 0.64 * volume.g, stratus);
  float baseShape = (volume.g - 0.55) * mix(0.27, 0.12, stratus);
  float h = (altitude - base - baseShape) / max(0.05, layerHeight);
  if (h >= 1.0) return 0.0;

  vec3 types = cloudTypes(weather.g);
  vec3 profiles = vec3(cloudProfile(h, 0.091, 0.42, 1.0),
    cloudProfile(h, 0.080, 0.51, 1.0), cloudProfile(h, 0.064, 0.61, 1.0));
  float profile = dot(profiles, types) / max(1.0, dot(types, vec3(1.0)));
  profile = mix(profile, cloudProfile(h, 0.12, 0.70, 1.0), stratus);

  float coherentShape = mix(volume.r, volume.g, 0.38);
  float shape = mix(coherentShape, 0.69, 0.17 * (1.0 - smoothstep(0.025, 0.21, h)));
  float cut = mix(0.74, 0.27, coverage) + stratus * (1.0 - volume.g) * 0.22;
  float body = shape - cut - (1.0 - profile) * 0.40;
  if (body <= 0.0) return 0.0;

  if (detail) {
    vec3 erosionUV = bodyUV * 4.83 + vec3(0.35, 0.54, 0.13);
    erosionUV.xz -= cloudWindVelocity * (uWindTime * 0.21);
    erosionUV += vec3(volume.b, volume.g, volume.r) * 0.12;
    vec3 erosion = textureLod(uDetail, erosionUV, 0.0).rgb;
    float holes = 1.0 - dot(erosion, vec3(0.51, 0.32, 0.17));
    float erosionStrength = mix(0.268, 0.177, weather.g) + 0.037 * stratus;
    body -= holes * erosionStrength * smoothstep(0.02, 0.20, h);
  }
  return smoothstep(0.0, 0.15, body) * body * profile * mix(4.5, 5.3, weather.g);
}

float cloudHighDensity(vec3 p, float altitude, vec4 weather, float coverage, bool detail) {
  if (coverage < 0.015) return 0.0;
  float measuredTop = weather.b * 18.0;
  float base = 6.15 - 0.4 * coverage;
  float ceiling = 0.26 + 2.7 * pow(coverage, 1.45);
  if (weather.b > 0.001) {
    base = clamp(measuredTop - mix(1.30, 2.60, weather.g), 3.2, 12.8);
    ceiling = max(0.24, measuredTop - base);
  }
  ceiling *= sqrt(max(0.2, uThickness));
  if (altitude < base || altitude >= base + 1.18 * ceiling) return 0.0;

  vec2 windPosition = p.xz - cloudWindVelocity * (uWindTime * 1.27);
  vec2 cellPosition = vec2(dot(vec2(0.913, 0.408), windPosition),
    dot(vec2(-0.408, 0.913), windPosition));
  // A fixed Y slice grades a thin high layer by its horizontal cells and wisps.
  vec3 cells = textureLod(uShape, vec3(cellPosition.x * 0.108, 0.623, cellPosition.y * 0.175), 0.0).rgb;
  float billows = mix(1.0, smoothstep(0.26, 0.76, cells.g), weather.g);
  float upper = base + ceiling * mix(0.81, 1.12, billows);
  float h = (altitude - base) / max(0.12, upper - base);
  if (h < 0.0 || h >= 1.0) return 0.0;
  float wisps = cells.b;
  if (detail) {
    wisps = textureLod(uDetail, vec3(cellPosition.x * 0.142, 0.314, cellPosition.y * 0.68), 0.0).r;
  }
  float feather = cloudProfile(h, 0.18, 0.44, 1.0);
  float softness = mix(0.22, 0.105, weather.a);
  float filling = smoothstep(0.62 - 0.57 * coverage, 0.62 - 0.57 * coverage + softness,
    mix(wisps, cells.r, 0.53));
  return filling * feather * coverage * mix(0.65, 1.34, billows);
}

float cloudDensity(vec3 p, bool detail) {
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
  float q = max(0.012, (1.0 - g) * (1.0 - g) + 2.0 * g * (1.0 - cosine));
  return (1.0 - g * g) * inversesqrt(q) / q;
}

vec2 cloudLight(vec3 p, vec3 sun, bool withDiffusion, float boundary) {
  float distance = 0.25;
  int lightSteps = clamp(uLightSteps, 2, 8);
  float cloudPath = mix(14.0, 5.8, smoothstep(0.0, 0.8, sun.y));
  float interval = cloudPath * 0.67 / (pow(1.67, float(lightSteps)) - 1.0);
  // Resolve the nearby erosion lobes before moving to coarser solar samples.
  float directDepth = cloudDensity(p + sun * 0.14, true) * distance;
  float isotropic = withDiffusion ? 1.0 - exp(-0.57 * directDepth) : 0.0;
  for (int j = 0; j < 8; ++j) {
    if (j >= lightSteps) break;
    float sampleDistance = distance + interval * 0.56;
    float section = cloudDensity(p + sun * sampleDistance, false) * interval;
    if (withDiffusion) {
      // One-dimensional Green kernel with slower attenuation than ballistic
      // transport. Deposited energy near edges feeds the built-up cloud field.
      float transport = exp(-0.115 * sampleDistance - 0.15 * directDepth);
      isotropic += transport * (1.0 - exp(-0.57 * section)) / (1.0 + 0.22 * distance);
    }
    directDepth += section;
    interval *= 1.67;
    distance += interval / 1.67;
    if (directDepth > 16.0 && !withDiffusion) break;
  }
  float build = 1.0 - exp(-0.77 * directDepth);
  return vec2(directDepth, (1.0 - exp(-0.88 * isotropic)) * build * boundary);
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

// Low-cloud projected occlusion for the surface and islands.
float cloudShadow(vec3 p, vec3 sun) {
  if (sun.y <= 0.015) return 1.0;
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
  float start = min(low.x, high.x);
  float end = max(low.y, high.y);
  if (start >= end) return vec4(0.0);

  int steps = clamp(uCloudSteps, 12, 104);
  float span = end - start;
  float baseStep = max(0.072, span / float(steps));
  float cosTheta = clamp(dot(ray, sun), -1.0, 1.0);
  float phase = 0.105 + 0.145 * cloudHg(cosTheta, 0.64) + 0.042 * cloudHg(cosTheta, -0.28);
  float secondOrder = 0.16 + 0.12 * cloudHg(cosTheta, 0.38);
  float day = smoothstep(-0.09, 0.39, sun.y);
  float sunVisible = smoothstep(-0.115, 0.045, sun.y);
  bool withDiffusion = uDiffusion > 0.001 && uDebugCloud != 2;
  float sampleFraction = 0.30 + 0.40 * clamp(jitter, 0.0, 1.0);
  float transmittance = 1.0;
  vec3 radiance = vec3(0.0);
  float weightedDistance = 0.0;
  float t = start;
  float skipped = 0.0;

  for (int i = 0; i < 104; ++i) {
    if (i >= steps || t >= end || transmittance < 0.008) break;
    bool inLow = t >= low.x && t < low.y;
    bool inHigh = t >= high.x && t < high.y;
    if (!inLow && !inHigh) {
      t = min(t < low.x ? low.x : 1.0e7, t < high.x ? high.x : 1.0e7);
      skipped = 0.0;
      continue;
    }
    float layerEnd = max(inLow ? low.y : -1.0, inHigh ? high.y : -1.0);
    float travel = clamp((t - start) / span, 0.0, 1.0);
    float distanceStep = max(0.085, (0.100 + t * 0.019) * 60.0 / float(steps));
    float stepSize = min(layerEnd - t, min(distanceStep, baseStep * (0.75 + 0.74 * travel)));
    float sampleDistance = t + sampleFraction * stepSize;
    vec3 p = eye + ray * sampleDistance;
    float rho = cloudDensity(p, true);
    if (rho < 0.012) {
      skipped = min(layerEnd - t, max(stepSize * 2.2, min(2.8, 0.31 + 0.046 * t)));
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
    } else if (uDebugCloud != 1 && contributing > 0.0003) {
      float boundary = withDiffusion ? cloudBoundaryConfidence(p, sun) : 0.0;
      vec2 optical = cloudLight(p, sun, withDiffusion, boundary);
      float shadow = exp(-optical.x);
      float upperLight = smoothstep(1.2, 6.0, cloudAltitude(p));
      vec3 ambient = mix(vec3(0.017, 0.019, 0.032), vec3(0.17, 0.24, 0.36), day)
        * (0.70 + 0.48 * upperLight) * mix(0.73, 1.0, shadow);
      vec3 direct = uSunColor * sunVisible * (phase * shadow * 0.85
        + secondOrder * 0.34 * exp(-0.57 * optical.x) + 0.030 * exp(-0.21 * optical.x));
      float thickGate = smoothstep(0.03, 0.28, rho);
      vec3 diffuse = uSunColor * (0.43 * sunVisible * uDiffusion * optical.y * thickGate);
      vec3 light = ambient + direct + diffuse;
      if (uDebugCloud == 2) light = direct;
      if (uDebugCloud == 3) light = diffuse;
      float air = 1.0 - exp(-0.0043 * sampleDistance);
      vec3 haze = mix(vec3(0.34, 0.19, 0.090), vec3(0.41, 0.57, 0.76), day);
      if (uDebugCloud == 0) light = mix(light, haze, air * (0.44 + 0.36 * day));
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
