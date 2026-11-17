import { cloudSource } from './cloud-volume.js';
import { oceanSource } from './ocean-background.js';
import { isletSource } from './islet.js';

const header = `#version 300 es
precision highp float;
precision highp int;
precision highp sampler3D;

const float PI = 3.141592653589793;
const float MAX_RANGE = 180.0;
`;

const view = `
in vec2 vUV;
uniform vec3 uEye, uForward, uRight, uUp, uSun, uLocalUp;
uniform vec2 uLens;

vec3 viewRay(vec2 uv) {
  vec2 d = (uv * 2.0 - 1.0) * uLens;
  return normalize(uForward + d.x * uRight + d.y * uUp);
}

// Spherical ocean horizon avoids the flat-plane seam on long grazing rays.
float seaDistance(vec3 eye, vec3 ray) {
  const float radius = 6371.0;
  float b = dot(eye, ray) + radius * ray.y;
  float c = dot(eye.xz, eye.xz) + eye.y * (2.0 * radius + eye.y);
  float d = b * b - c;
  if (b >= 0.0 || d <= 0.0) return MAX_RANGE;
  return min(MAX_RANGE, c / (-b + sqrt(d)));
}
`;

export const fullVertex = header + `
out vec2 vUV;
void main() {
  vec2 p = vec2(gl_VertexID == 1 ? 3.0 : -1.0, gl_VertexID == 2 ? 3.0 : -1.0);
  vUV = p * 0.5 + 0.5;
  gl_Position = vec4(p, 0.0, 1.0);
}
`;

export const marchFragment = header + view + cloudSource + `
uniform int uFrame;
uniform float uCloudRange;
layout(location=0) out vec4 fog;
layout(location=1) out float range;

float pixelJitter() {
  // Keep each pixel on an independent, temporally stratified sequence.
  uvec2 p = uvec2(gl_FragCoord.xy);
  uint n = p.x * 1597334677u ^ p.y * 3812015801u;
  n ^= n >> 16u;
  n *= 2246822519u;
  n ^= n >> 13u;
  return fract(float(n & 65535u) / 65536.0 + float(uFrame) * 0.61803398875);
}

void main() {
  vec3 ray = viewRay(vUV);
  float distanceToCloud;
  float upper = min(uCloudRange, seaDistance(uEye, ray));
  fog = marchCloud(uEye, ray, uSun, upper, pixelJitter(), distanceToCloud);
  fog *= 1.0 - 0.94 * smoothstep(uCloudRange * 0.81, uCloudRange, distanceToCloud);
  range = clamp(distanceToCloud / MAX_RANGE, 0.0, 1.0);
}
`;

export const historyFragment = header + view + `
uniform sampler2D uCurrent, uCurrentRange, uPrevious, uPreviousRange;
uniform vec3 uPreviousEye, uPreviousForward, uPreviousRight, uPreviousUp;
uniform vec2 uPreviousLens;
uniform float uHistoryWeight;
uniform bool uSameView;
layout(location=0) out vec4 fog;
layout(location=1) out float range;

void main() {
  vec4 now = texture(uCurrent, vUV);
  range = texture(uCurrentRange, vUV).r;
  fog = now;
  if (uHistoryWeight <= 0.01) return;
  if (uSameView) {
    vec4 still = texture(uPrevious, vUV);
    float oldRange = texture(uPreviousRange, vUV).r;
    fog = mix(now, still, uHistoryWeight);
    if (fog.a > 0.001) range = mix(range * now.a, oldRange * still.a, uHistoryWeight) / fog.a;
    return;
  }
  if (now.a <= 0.003) return;
  float depth = range * MAX_RANGE;
  vec3 lastPosition = uEye + viewRay(vUV) * depth - uPreviousEye;
  float forwardDistance = dot(lastPosition, uPreviousForward);
  if (forwardDistance <= 0.0) return;
  vec2 q = vec2(dot(lastPosition, uPreviousRight), dot(lastPosition, uPreviousUp))
    / (forwardDistance * uPreviousLens) * 0.5 + 0.5;
  if (any(lessThan(q, vec2(0.005))) || any(greaterThan(q, vec2(0.995)))) return;
  vec4 before = texture(uPrevious, q);
  float oldDepth = texture(uPreviousRange, q).r * MAX_RANGE;
  float distanceError = abs(length(lastPosition) - oldDepth);
  if (before.a < 0.002 || distanceError > 0.7 + depth * 0.08) return;

  // A clamped history value won't drag a dark rim over a newly exposed gap.
  vec2 delta = 1.0 / vec2(textureSize(uCurrent, 0));
  vec4 a = texture(uCurrent, vUV + vec2(delta.x, 0.0));
  vec4 b = texture(uCurrent, vUV - vec2(delta.x, 0.0));
  vec4 c = texture(uCurrent, vUV + vec2(0.0, delta.y));
  vec4 d = texture(uCurrent, vUV - vec2(0.0, delta.y));
  vec4 minimum = min(now, min(min(a,b), min(c,d)));
  vec4 maximum = max(now, max(max(a,b), max(c,d)));
  float agreement = (1.0 - smoothstep(0.12, 0.62, abs(before.a - now.a)))
    * (1.0 - 0.85 * smoothstep(0.4, 0.75 + depth * 0.079, distanceError));
  fog = mix(now, clamp(before, minimum - 0.033, maximum + 0.033), uHistoryWeight * agreement);
}
`;

export const skyFragment = header + `
in vec2 vUV;
uniform float uSunAltitude;
uniform float uEyeAltitude;
uniform float uAtmosphereScale;
layout(location=0) out vec4 sky;

const float PLANET = 6371.0;
const float ATMOSPHERE = 6451.0;
const vec3 BETA_R = vec3(0.0058, 0.0135, 0.0331);
const vec3 BETA_O = vec3(0.00061, 0.00188, 0.000085);
const float BETA_M = 0.0037;
const float EXT_M = 0.0044;

float frontSphere(vec3 p, vec3 d, float radius) {
  float b = dot(d, p);
  float q = b * b - dot(p,p) + radius * radius;
  return q < 0.0 ? -1.0 : -b - sqrt(q);
}

float exitSphere(vec3 p, vec3 d, float radius) {
  float b = dot(d, p);
  return -b + sqrt(max(0.0, b * b - dot(p,p) + radius * radius));
}

vec3 airDensity(vec3 p) {
  float h = max(0.0, length(p) - PLANET);
  return vec3(exp(-h / 8.0), exp(-h / 1.2), max(0.0, 1.0 - abs(h - 24.0) / 16.0));
}

vec3 airExtinction(vec3 depth) {
  return exp(-(BETA_R * depth.x + EXT_M * depth.y + BETA_O * depth.z));
}

vec3 sunlightAt(vec3 p, vec3 sun) {
  if (frontSphere(p, sun, PLANET) > 0.0) return vec3(0.0);
  float length = exitSphere(p, sun, ATMOSPHERE);
  vec3 optical = vec3(0);
  float prior = 0.0;
  for (int i = 1; i <= 7; i++) {
    float u = float(i) / 7.0;
    float t = length * u * u;
    optical += airDensity(p + sun * (0.5 * (prior + t))) * (t - prior);
    prior = t;
  }
  return airExtinction(optical);
}

void main() {
  float phi = (vUV.x - 0.5) * 2.0 * PI;
  float elevation = pow(vUV.y, 1.75) * 0.5 * PI;
  vec3 d = vec3(sin(phi) * cos(elevation), sin(elevation), cos(phi) * cos(elevation));
  vec3 sun = vec3(0.0, sin(uSunAltitude), cos(uSunAltitude));
  vec3 eye = vec3(0.0, PLANET + max(0.025, uEyeAltitude), 0.0);
  float distanceThroughAir = exitSphere(eye, d, ATMOSPHERE);
  vec3 optical = vec3(0.0);
  vec3 scattering = vec3(0.0);
  float cosine = dot(d, sun);
  float rPhase = 0.05968 * (1.0 + cosine * cosine);
  float g = 0.77;
  float mPhase = 0.07958 * (1.0 - g * g) / pow(max(0.015, 1.0 + g * g - 2.0 * g * cosine), 1.5);
  float prior = 0.0;
  for (int i = 1; i <= 18; i++) {
    float fraction = float(i) / 18.0;
    float t = distanceThroughAir * fraction * fraction;
    float stepLength = t - prior;
    vec3 p = eye + d * (0.5 * (t + prior));
    vec3 density = airDensity(p);
    vec3 toSun = sunlightAt(p, sun);
    vec3 toObserver = airExtinction(optical + density * stepLength * 0.5);
    scattering += toSun * toObserver * (BETA_R * density.x * rPhase + BETA_M * density.y * mPhase) * stepLength;
    optical += density * stepLength;
    prior = t;
  }
  vec3 optics = scattering * 11.4;
  float dusk = 1.0 - smoothstep(0.033, 0.26, sun.y);
  vec3 marineColor = mix(vec3(0.52, 0.78, 1.05), vec3(1.02, 0.73, 0.44), dusk * exp(-elevation * 5.7));
  sky = vec4((optics * marineColor + vec3(0.003, 0.005, 0.011)) / uAtmosphereScale, 1.0);
}
`;

export const compositeFragment = header + view + cloudSource + oceanSource + isletSource + `
uniform sampler2D uFog, uRange, uSkyLUT;
uniform vec3 uIsland;
uniform float uIslandHeading;
uniform float uAtmosphereScale;
uniform float uTime;
uniform float uExposure;
out vec4 color;

vec3 clearSky(vec3 direction) {
  vec3 sunTangent = normalize(uSun - dot(uSun, uLocalUp) * uLocalUp);
  float phi = atan(dot(cross(sunTangent, direction), uLocalUp), dot(direction, sunTangent));
  float elevation = asin(clamp(dot(direction, uLocalUp), 0.0, 1.0));
  vec2 skyUV = vec2(phi / (2.0 * PI) + 0.5, pow(elevation / (0.5 * PI), 1.0 / 1.75));
  return texture(uSkyLUT, skyUV).rgb * uAtmosphereScale;
}

vec4 visibleFog(vec2 uv, out float depth) {
  vec2 scale = vec2(textureSize(uFog, 0));
  vec2 cell = uv * scale - 0.5;
  vec2 base = floor(cell);
  vec2 f = fract(cell);
  float depthRef = texture(uRange, uv).r * MAX_RANGE;
  vec4 data = vec4(0.0);
  float total = 0.0;
  float depthSum = 0.0;
  float opacitySum = 0.0;
  for (int j = 0; j < 2; ++j) {
    for (int i = 0; i < 2; ++i) {
      vec2 at = (base + vec2(i, j) + 0.5) / scale;
      vec4 cloud = texture(uFog, at);
      float range = texture(uRange, at).r * MAX_RANGE;
      float bilinear = (i == 0 ? 1.0 - f.x : f.x) * (j == 0 ? 1.0 - f.y : f.y);
      float proximity = mix(0.42, 1.0, exp(-abs(range - depthRef) / max(1.0, depthRef * 0.16)));
      float weight = bilinear * proximity;
      data += cloud * weight;
      total += weight;
      depthSum += range * weight * cloud.a;
      opacitySum += weight * cloud.a;
    }
  }
  depth = depthSum / max(0.0001, opacitySum);
  return data / max(0.0001, total);
}

vec3 toDisplay(vec3 c) {
  c = max(c * uExposure, vec3(0.0));
  c = (c * (2.51 * c + 0.03)) / (c * (2.43 * c + 0.59) + 0.14);
  return pow(clamp(c, 0.0, 1.0), vec3(1.0 / 2.2));
}

void main() {
  vec3 ray = viewRay(vUV);
  float surface = seaDistance(uEye, ray);
  vec3 air = clearSky(ray);
  float angle = length(ray - uSun);
  float sunRadius = 0.009;
  float sunDisk = 1.0 - smoothstep(sunRadius - 0.001, sunRadius + 0.002, angle);
  float glow = 0.18 * exp(-angle * 32.0);
  vec3 background = air + uSunColor * (sunDisk * 18.0 + glow);
  float cs = cos(uIslandHeading);
  float sn = sin(uIslandHeading);
  mat2 islandLocal = mat2(cs, sn, -sn, cs);
  vec3 originToEye = uEye - uIsland;
  vec2 islandEye = islandLocal * originToEye.xz;
  vec2 islandRay = islandLocal * ray.xz;
  vec2 islandSun = islandLocal * uSun.xz;
  vec4 land = traceIslet(vec3(islandEye.x, originToEye.y, islandEye.y),
    vec3(islandRay.x, ray.y, islandRay.y), vec3(0.0),
    vec3(islandSun.x, uSun.y, islandSun.y), uSunColor, cloudShadow(uIsland, uSun));
  bool foregroundLand = land.a < surface;
  if (foregroundLand) {
    background = mix(land.rgb, air, 1.0 - exp(-land.a * 0.028));
  } else if (surface < MAX_RANGE) {
    vec3 p = uEye + ray * surface;
    vec3 seaNormal = normalize(vec3(p.x, 6371.0 + p.y, p.z));
    vec3 mirror = reflect(ray, seaNormal);
    vec3 reflectSky = clearSky(mirror);
    float shade = cloudShadow(p, uSun);
    vec3 waterRay = vec3(ray.x, dot(ray, seaNormal), ray.z);
    vec3 waterSun = vec3(uSun.x, dot(uSun, seaNormal), uSun.z);
    background = oceanColor(uEye, waterRay, surface, waterSun, uSunColor, reflectSky, shade, uTime, uIsland.xz);
    float blueHaze = 1.0 - exp(-surface * (0.018 + (1.0 - smoothstep(0.04, 0.22, waterSun.y)) * 0.019));
    background = mix(background, air, blueHaze * 0.96);
  }

  float depth;
  vec4 fog = visibleFog(vUV, depth);
  if (foregroundLand && depth > land.a) fog = vec4(0.0);
  if (uDebugCloud == 1 || uDebugCloud == 4) background *= 0.34;
  if (uDebugCloud != 1 && uDebugCloud != 4) {
    float aerial = 1.0 - exp(-depth * (0.010 + 0.009 * exp(-max(0.0, ray.y) * 10.0)));
    fog.rgb = mix(fog.rgb, air * fog.a, aerial * 0.84);
  }
  color = vec4(toDisplay(fog.rgb + (1.0 - fog.a) * background), 1.0);
}
`;
