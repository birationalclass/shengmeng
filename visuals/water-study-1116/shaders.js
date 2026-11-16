import { opticsSource } from './optics.js';
import { surfaceSource } from './water-surface.js';

const begin = `#version 300 es
precision highp float;
precision highp int;
`;

const common = `
uniform vec3 uEye;
uniform vec3 uSun;
uniform vec3 uLight;
uniform vec2 uViewport;
uniform float uClarity;
uniform int uSetting;

vec3 displayColor(vec3 c) {
  c = max(vec3(0.0), c * 1.07);
  // Filmic shoulder, followed by the display transfer.
  c = (c * (2.51 * c + 0.03)) / (c * (2.43 * c + 0.59) + 0.14);
  return pow(clamp(c, 0.0, 1.0), vec3(1.0 / 2.2));
}

vec3 environment(vec3 direction) {
  float horizon = 1.0 - smoothstep(0.015, 0.68, max(direction.y, 0.0));
  vec3 upper = uSetting == 2 ? vec3(0.23, 0.44, 0.78) : vec3(0.19, 0.31, 0.52);
  vec3 color = mix(upper, vec3(0.74, 0.83, 0.95), horizon);
  color += uLight * (0.048 * pow(max(0.0, dot(direction, uSun)), 19.0));
  if (direction.y < 0.0) {
    color = mix(vec3(0.028, 0.036, 0.041), vec3(0.11, 0.14, 0.16),
      exp(direction.y * 40.0));
  }
  return color;
}

vec3 air(vec3 c, float distanceToEye) {
  float fog = smoothstep(34.0, 110.0, distanceToEye);
  return mix(c, vec3(0.18, 0.22, 0.25), fog * 0.8);
}
`;

const shadows = `
uniform sampler2D uShadow;
uniform mat4 uSunMatrix;

float lightVisibility(vec3 p, vec3 n) {
  vec4 clip = uSunMatrix * vec4(p + n * 0.045, 1.0);
  vec3 projected = clip.xyz / clip.w * 0.5 + 0.5;
  if (any(lessThan(projected, vec3(0.0))) || any(greaterThan(projected, vec3(1.0)))) return 1.0;
  vec2 texel = 1.0 / vec2(textureSize(uShadow, 0));
  float visible = 0.0;
  for (int y = -1; y <= 1; y++) {
    for (int x = -1; x <= 1; x++) {
      float blockedAt = texture(uShadow, projected.xy + vec2(x, y) * texel * 1.2).r;
      visible += step(projected.z - 0.0009, blockedAt);
    }
  }
  return visible / 9.0;
}
`;

const groundNoise = `
uint rockHash(ivec3 cell) {
  uvec3 u = uvec3(cell);
  uint n = u.x * 1597334677u ^ u.y * 3812015801u ^ u.z * 958689233u;
  n ^= n >> 16u;
  n *= 2246822519u;
  n ^= n >> 13u;
  return n;
}

float rockLattice(ivec3 p) {
  return float(rockHash(p) & 65535u) / 65535.0;
}

float rockNoise(vec3 p) {
  ivec3 q = ivec3(floor(p));
  vec3 t = fract(p);
  t = t * t * (3.0 - 2.0 * t);
  return mix(
    mix(mix(rockLattice(q), rockLattice(q + ivec3(1,0,0)), t.x),
        mix(rockLattice(q + ivec3(0,1,0)), rockLattice(q + ivec3(1,1,0)), t.x), t.y),
    mix(mix(rockLattice(q + ivec3(0,0,1)), rockLattice(q + ivec3(1,0,1)), t.x),
        mix(rockLattice(q + ivec3(0,1,1)), rockLattice(q + ivec3(1,1,1)), t.x), t.y), t.z);
}

// Rock colours and micro-relief are generated in 3D so the same features
// continue across faces and while moving the camera.
vec3 rockMaterial(vec3 p, float palette, out float relief) {
  vec3 warp = vec3(rockNoise(p * 1.19 + 3.6), rockNoise(p * 0.99 + 7.3),
    rockNoise(p * 1.26 + 16.3)) - 0.5;
  vec3 q = p + 0.49 * warp;
  float broad = rockNoise(q * 2.8);
  float medium = rockNoise(q * 8.4);
  float detail = rockNoise(q * 25.3);
  float grit = rockNoise(p * 77.0);
  float strata = 0.5 + 0.5 * sin((q.y + q.z * 0.27 - q.x * 0.18) * 15.1 + broad * 4.9 + medium);
  float fissure = 1.0 - (1.0 - smoothstep(0.014, 0.075, abs(broad + 0.19 * medium - 0.54)))
    * smoothstep(0.43, 0.73, rockNoise(p * 2.20 + 41.0));
  float strataEdge = smoothstep(0.035, 0.16, strata);
  relief = broad * 0.23 + medium * 0.22 + detail * 0.13 + grit * 0.017 + strataEdge * 0.062 + fissure * 0.075;
  vec3 shale = mix(vec3(0.036, 0.044, 0.047), vec3(0.21, 0.17, 0.095), palette);
  vec3 stone = mix(vec3(0.18, 0.20, 0.20), vec3(0.67, 0.54, 0.34), palette);
  vec3 color = mix(shale, stone, smoothstep(0.17, 0.80, broad * 0.35 + medium * 0.30 + detail * 0.23 + grit * 0.12));
  float lichen = smoothstep(0.46, 0.70, rockNoise(q * 3.3 + 3.1) * 0.45 + medium * 0.2 + detail * 0.35) * palette;
  color = mix(color, vec3(0.26, 0.251, 0.103) * (0.72 + detail * 0.7), lichen * 0.79);
  return color * mix(0.47, 1.23, fissure) * mix(0.73, 1.08, strataEdge) * mix(0.76, 1.28, grit);
}

vec2 lensOffset(vec2 p) {
  return vec2(rockNoise(vec3(p * 0.45, uTime * 0.22)),
    rockNoise(vec3(p * 0.49 + 13.5, uTime * 0.18 + 7.2))) - 0.5;
}

vec2 seedOffset(vec2 cell) {
  return vec2(rockLattice(ivec3(ivec2(cell), 3)), rockLattice(ivec3(ivec2(cell), 21)));
}

float causticFilaments(vec2 p) {
  vec2 cell = floor(p);
  vec2 local = fract(p);
  float closest = 8.0;
  float next = 8.0;
  for (int y = -1; y <= 1; y++) {
    for (int x = -1; x <= 1; x++) {
      vec2 neighbor = vec2(x, y);
      vec2 delta = neighbor + 0.78 * seedOffset(cell + neighbor) - local;
      float d = dot(delta, delta);
      next = min(next, max(d, closest));
      closest = min(closest, d);
    }
  }
  return (1.0 - smoothstep(0.010, 0.070, next - closest))
    + 0.34 * (1.0 - smoothstep(0.021, 0.17, next - closest));
}

float causticLight(vec3 world, float depth) {
  vec2 p = world.xz + uSun.xz * depth * 0.36;
  float offset = 0.074;
  vec2 dx = vec2(offset, 0.0);
  vec2 dz = vec2(0.0, offset);
  vec2 sx = (windSlope(p + dx, 0.012) - windSlope(p - dx, 0.012)) / (offset * 2.0);
  vec2 sz = (windSlope(p + dz, 0.012) - windSlope(p - dz, 0.012)) / (offset * 2.0);
  float focusDistance = min(depth * 0.19, 0.56);
  float area = determinant(mat2(1.0 + sx.x * focusDistance, sx.y * focusDistance,
    sz.x * focusDistance, 1.0 + sz.y * focusDistance));
  float focus = clamp(0.6 / (0.30 + abs(area)), 0.3, 1.7);
  vec2 slope = waterSlope(p, 0.018);
  vec2 warped = p * 1.85 + 1.34 * lensOffset(p) + slope * 0.72
    + vec2(uTime * 0.13, -uTime * 0.08);
  float threads = causticFilaments(warped);
  return threads * (0.62 + focus) * smoothstep(0.01, 0.28, depth) * exp(-depth * .16);
}
`;

export const fullVertex = begin + `
out vec2 vUV;
void main() {
  vec2 p = vec2(gl_VertexID == 1 ? 3.0 : -1.0, gl_VertexID == 2 ? 3.0 : -1.0);
  vUV = p * 0.5 + 0.5;
  gl_Position = vec4(p, 0.0, 1.0);
}
`;

export const skyFragment = begin + common + `
in vec2 vUV;
uniform vec3 uForward, uRight, uUp;
uniform float uLens;
out vec4 frag;
void main() {
  vec2 p = (vUV * 2.0 - 1.0) * vec2(uViewport.x / uViewport.y, 1.0);
  vec3 ray = normalize(uForward + uLens * (p.x * uRight + p.y * uUp));
  vec3 color = environment(ray);
  if (uSetting == 2 && ray.y < 0.0) {
    color = mix(vec3(0.56, 0.55, 0.52), vec3(0.72, 0.76, 0.81), exp(ray.y * 24.0));
  } else if (uSetting != 2 && ray.y <= 0.0) {
    color = mix(environment(vec3(ray.x, 0.0, ray.z)), color, smoothstep(0.0, 0.032, -ray.y));
  }
  float distanceToSun = length(ray - uSun);
  float nearHorizon = 1.0 - smoothstep(0.095, 0.23, uSun.y);
  if (uSetting == 2) {
    color = mix(color, color * vec3(0.64, 0.53, 0.41), nearHorizon);
    color += vec3(1.0, 0.59, 0.26) * exp(-distanceToSun * 6.6) * nearHorizon;
  }
  float sun = 2.9 * (1.0 - smoothstep(0.016, 0.021, distanceToSun)) + 0.21 * exp(-distanceToSun * 36.0);
  frag = vec4(color + uLight * sun, 1.0);
}
`;

export const displayFragment = begin + common + `
uniform sampler2D uColor;
in vec2 vUV;
out vec4 frag;
void main() {
  frag = vec4(displayColor(texture(uColor, vUV).rgb), 1.0);
}
`;

export const shadowVertex = begin + `
layout(location=0) in vec3 aPosition;
uniform mat4 uSunMatrix, uModel;
void main() {
  gl_Position = uSunMatrix * uModel * vec4(aPosition, 1.0);
}
`;

export const shadowFragment = begin + `void main() {}`;

export const crestShadowVertex = begin + surfaceSource + `
layout(location=0) in vec2 aSheet;
uniform mat4 uSunMatrix;
void main() {
  gl_Position = uSunMatrix * vec4(crestPosition(aSheet), 1.0);
}
`;

export const terrainVertex = begin + `
layout(location=0) in vec3 aPosition;
layout(location=1) in vec3 aNormal;
layout(location=2) in vec2 aMaterial;
uniform mat4 uViewProjection, uModel;
out vec3 vWorld, vNormal, vObject;
out vec2 vMaterial;
void main() {
  vObject = aPosition;
  vec4 world = uModel * vec4(aPosition, 1.0);
  vWorld = world.xyz;
  vNormal = mat3(uModel) * aNormal;
  vMaterial = aMaterial;
  gl_Position = uViewProjection * world;
}
`;

export const terrainFragment = begin + common + surfaceSource + shadows + groundNoise + `
uniform bool uCaustics;
in vec3 vWorld, vNormal, vObject;
in vec2 vMaterial;
out vec4 frag;
void main() {
  vec3 n = normalize(vNormal);
  vec3 p = vWorld;
  vec3 albedo = vec3(0.5);
  float roughness = 0.75;
  float submerged = uSetting == 2 ? 0.0 : 1.0 - smoothstep(-0.018, 0.03, p.y);
  if (vMaterial.x < 0.5) {
    float relief;
    albedo = rockMaterial(p, vMaterial.y, relief);
    vec3 px = dFdx(p);
    vec3 py = dFdy(p);
    vec3 yEdge = cross(py, n);
    vec3 xEdge = cross(n, px);
    float determinant = dot(px, yEdge);
    if (abs(determinant) > 1e-7) {
      vec3 surfaceGradient = (dFdx(relief) * yEdge + dFdy(relief) * xEdge) / determinant;
      n = normalize(n - surfaceGradient * mix(0.155, 0.061, smoothstep(5.0, 25.0, distance(p, uEye))));
    }
    float damp = submerged + (1.0 - submerged) * (1.0 - smoothstep(0.02, 0.41, p.y)) * 0.74;
    albedo *= mix(1.0, 0.64, damp);
    roughness = mix(0.84, 0.37, damp);
  } else if (vMaterial.x < 1.5) {
    float gravel = rockNoise(p * 38.0);
    float sand = rockNoise(p * 2.7);
    float veins = 0.5 + 0.5 * sin(p.x * 2.1 + p.z * 1.4 + rockNoise(p * 0.60) * 8.3);
    albedo = mix(vec3(0.21, 0.23, 0.17), vec3(0.62, 0.55, 0.39),
      sand * 0.54 + gravel * 0.31 + veins * 0.15);
  } else if (vMaterial.x < 2.5) {
    albedo = mix(vec3(0.57, 0.54, 0.48), vec3(0.69, 0.67, 0.63), vMaterial.y);
  } else {
    float grain = rockNoise(vObject * vec3(72.0, 66.0, 5.2));
    float streaks = rockNoise(vObject * vec3(11.0, 46.0, 3.9));
    albedo = mix(vec3(0.11, 0.027, 0.008), vec3(0.47, 0.166, 0.046),
      vMaterial.y * 0.62 + 0.23 * grain + 0.15 * streaks);
    if (vMaterial.x > 3.5 && vMaterial.x < 4.5) {
      albedo = mix(vec3(0.27, 0.13, 0.041), vec3(0.74, 0.48, 0.22),
        vMaterial.y * 0.56 + grain * 0.20 + streaks * 0.24);
    } else if (vMaterial.x >= 4.5) {
      albedo = (0.48 + 0.52 * grain) * vec3(0.055, 0.035, 0.023);
    }
    roughness = 0.45;
  }

  float visible = lightVisibility(p, n);
  float sunCos = max(0.0, dot(n, uSun));
  vec3 directionToEye = normalize(uEye - p);
  vec3 halfVector = normalize(directionToEye + uSun);
  float sheen = pow(max(0.0, dot(n, halfVector)), mix(75.0, 9.0, roughness)) * mix(0.15, 0.024, roughness);
  float sky = 0.12 + 0.23 * max(0.0, n.y);
  vec3 direct = (albedo * sunCos * 0.40 + sheen) * uLight * visible;
  if (uCaustics && submerged > 0.01 && p.y > -7.0 && visible > 0.05) {
    direct += albedo * vec3(0.44, 0.89, 1.00) * 2.65 * causticLight(p, -p.y)
      * (0.25 + 0.75 * sunCos) * (0.25 + 0.75 * visible) * uClarity;
  }
  vec3 color = albedo * vec3(0.64, 0.75, 0.89) * sky + direct;
  frag = vec4(air(color, distance(p, uEye)), 1.0);
}
`;

export const waterVertex = begin + surfaceSource + `
layout(location=0) in vec2 aSheet;
uniform mat4 uViewProjection;
uniform int uSetting;
out vec3 vWorld, vCrestNormal;
out float vThickness;
void main() {
  vCrestNormal = vec3(0.0, 1.0, 0.0);
  vThickness = 1.0;
  if (uSetting == 2) {
    vec2 delta = vec2(0.003, 0.0);
    vec3 across = crestPosition(aSheet + delta) - crestPosition(aSheet - delta);
    vec3 along = crestPosition(aSheet + delta.yx) - crestPosition(aSheet - delta.yx);
    vWorld = crestPosition(aSheet);
    vCrestNormal = normalize(cross(along, across));
    vThickness = clamp(0.98 - 0.91 * aSheet.y + 0.08 * sin(aSheet.x * 9.0), 0.035, 1.0);
  } else {
    vWorld = vec3(aSheet.x, windHeight(aSheet) + impulse(aSheet), aSheet.y);
  }
  gl_Position = uViewProjection * vec4(vWorld, 1.0);
}
`;

export const waterFragment = begin + common + surfaceSource + shadows + opticsSource + `
uniform sampler2D uColor, uDepth;
uniform mat4 uViewProjection, uInverseViewProjection;
uniform float uRoughness;
uniform int uViewMode;
in vec3 vWorld, vCrestNormal;
in float vThickness;
out vec4 frag;

vec3 worldFromDepth(vec2 uv, float depth) {
  vec4 world = uInverseViewProjection * vec4(uv * 2.0 - 1.0, depth * 2.0 - 1.0, 1.0);
  return world.xyz / world.w;
}

bool projectToScene(vec3 p, out vec3 uvDepth) {
  vec4 clip = uViewProjection * vec4(p, 1.0);
  uvDepth = clip.xyz / clip.w * 0.5 + 0.5;
  return clip.w > 0.0 && all(greaterThan(uvDepth.xy, vec2(0.002)))
    && all(lessThan(uvDepth.xy, vec2(0.998)));
}

// March against the opaque depth buffer. Refraction only accepts the
// submerged geometry; reflection only accepts above-water geometry.
bool traceScene(vec3 origin, vec3 ray, float extent, bool reflection, out vec2 hitUV, out vec3 hitWorld) {
  float lastT = 0.03;
  for (int i = 1; i <= 15; i++) {
    float s = float(i) / 15.0;
    float t = 0.045 + extent * s * s;
    vec3 q;
    if (!projectToScene(origin + ray * t, q)) break;
    float old = texture(uDepth, q.xy).r;
    if (old < 0.99998 && q.z > old + 0.000014) {
      vec3 world = worldFromDepth(q.xy, old);
      bool valid = reflection ? world.y >= -0.055 : world.y <= 0.046 || uSetting == 2;
      if (valid && distance(origin + ray * t, world) < 0.22 + t * 0.18) {
        for (int refine = 0; refine < 3; refine++) {
          float mid = 0.5 * (lastT + t);
          vec3 halfUV;
          projectToScene(origin + ray * mid, halfUV);
          float halfDepth = texture(uDepth, halfUV.xy).r;
          if (halfUV.z > halfDepth + 0.000014) t = mid;
          else lastT = mid;
        }
        projectToScene(origin + ray * t, q);
        world = worldFromDepth(q.xy, texture(uDepth, q.xy).r);
        if (reflection ? world.y < -0.055 : world.y > 0.046 && uSetting != 2) {
          lastT = t;
          continue;
        }
        hitUV = q.xy;
        hitWorld = world;
        return true;
      }
    }
    lastT = t;
  }
  return false;
}

void main() {
  vec2 uv = gl_FragCoord.xy / uViewport;
  float sceneDepth = texture(uDepth, uv).r;
  if (gl_FragCoord.z > sceneDepth + 0.000009) discard;
  vec3 p = vWorld;
  vec3 view = normalize(uEye - p);
  float footprint = max(length(dFdx(p.xz)), length(dFdy(p.xz)));
  vec2 slope = waterSlope(p.xz, footprint);
  vec3 n = normalize(vec3(-slope.x, 1.0, -slope.y));
  float thickness = clamp(0.86 - p.y * 2.4 - length(slope) * 0.29, 0.16, 1.0);
  if (uSetting == 2) {
    n = normalize(vCrestNormal + vec3(-slope.x, 0.0, -slope.y) * 0.72);
    if (dot(n, view) < 0.0) n = -n;
    thickness = vThickness;
  }
  vec3 reflecting = reflect(-view, n);
  vec3 refracting = refract(-view, n, 1.0 / 1.333);
  if (refracting.y > -0.01 && uSetting != 2) refracting = normalize(vec3(refracting.x, -0.045, refracting.z));
  vec3 sky = environment(reflecting);
  vec3 reflection = sky;
  vec2 hitUV;
  vec3 hitWorld;

  float surfaceDistance = distance(uEye, p);
  if (uSetting != 2 && surfaceDistance < 36.0 && reflecting.y > -0.08 &&
      traceScene(p + n * 0.08, reflecting, 17.0, true, hitUV, hitWorld)) {
    vec2 frameEdge = min(hitUV, 1.0 - hitUV);
    float weight = smoothstep(0.005, 0.065, min(frameEdge.x, frameEdge.y));
    reflection = mix(sky, texture(uColor, hitUV).rgb, weight * 0.60);
  }

  vec3 transmission = vec3(0.095, 0.114, 0.090);
  float depth = uSetting == 2 ? 0.28 + thickness * 1.48 : 5.6;
  vec3 floorPoint = worldFromDepth(uv, min(sceneDepth, 0.99995));
  if (uSetting != 2 && sceneDepth < 0.99998 && floorPoint.y < 0.042) {
    depth = max(0.028, (p.y - floorPoint.y) / max(0.14, abs(refracting.y)));
    transmission = texture(uColor, uv).rgb;
    vec3 estimate = p + refracting * depth;
    vec3 estimateUV;
    if (projectToScene(estimate, estimateUV)) {
      float estimateDepth = texture(uDepth, estimateUV.xy).r;
      vec3 bottom = worldFromDepth(estimateUV.xy, min(estimateDepth, 0.99995));
      if (bottom.y < 0.023 && estimateDepth < 0.99998 && distance(bottom, estimate) < 2.0) {
        float agreement = 1.0 - smoothstep(0.15, 1.95, distance(bottom, estimate));
        transmission = mix(transmission, texture(uColor, estimateUV.xy).rgb, agreement);
        depth = mix(depth, max(0.028, distance(p, bottom)), agreement);
      }
    }
  }
  if (uSetting == 2) {
    float shallowEdge = 1.0 - smoothstep(0.0, 0.79, p.y);
    transmission = mix(vec3(0.010, 0.051, 0.065), texture(uColor, uv).rgb * vec3(0.27, 0.57, 0.65),
      shallowEdge * 0.78);
    depth *= mix(1.0, 0.33, shallowEdge);
  }
  if (uClarity > 0.60 && surfaceDistance < 33.0 && uSetting != 2 &&
      traceScene(p - n * 0.035, refracting, min(8.0, depth + 2.8), false, hitUV, hitWorld)) {
    transmission = mix(transmission, texture(uColor, hitUV).rgb, 0.76);
    depth = mix(depth, max(0.03, distance(p, hitWorld)), 0.76);
  }

  float shade = lightVisibility(p + vec3(0.0, 0.032, 0.0), vec3(0.0, 1.0, 0.0));
  float activeCrest = uSetting == 2 ? 0.0 : smoothstep(0.024, 0.10, impulse(p.xz));
  float foam = activeCrest * smoothstep(0.24, 0.59, length(slope)) * 0.31;
  vec3 color = waterOptics(n, view, uSun, reflection, transmission, thickness, depth,
    foam, uClarity, uRoughness, uViewMode, uLight * mix(0.04, 1.0, shade));
  if (uViewMode == 0 && uSetting != 2) {
    float ambientShadow = mix(0.69, 1.0, shade);
    color = air(color * ambientShadow, surfaceDistance);
  } else if (uViewMode == 0) {
    color = mix(texture(uColor, uv).rgb, color, smoothstep(-0.12, 0.105, p.y));
  }
  frag = vec4(displayColor(color), 1.0);
}
`;
