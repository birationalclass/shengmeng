export const skySource = `
float squared(float x) {
  return x * x;
}

float noise2(vec2 p) {
  vec2 cell = floor(p);
  vec2 fraction = fract(p);
  fraction = fraction * fraction * (3.0 - 2.0 * fraction);
  return texture2D(uNoise, (cell + fraction + 0.5) / 256.0).r;
}

// The five octaves use the demonstrated 2^i frequency and 1/2^i amplitude.
float cloudNoise(vec2 p) {
  float sum = 0.0;
  float amplitude = 0.5;
  mat2 rotate = mat2(0.8, -0.6, 0.6, 0.8);
  for (int i = 0; i < 5; i++) {
    sum += amplitude * noise2(p);
    p = 2.0 * rotate * p + vec2(19.6, 8.3);
    amplitude *= 0.5;
  }
  return sum;
}

vec3 atmosphere(vec3 ray, vec3 sun) {
  float y = max(ray.y, 0.0);
  if (uBands > 0.0) {
    float bands = floor(mix(4.0, 64.0, smoothstep(0.20, 0.77, uBuild)));
    y = mix(y, floor(y * bands + 0.35) / bands, uBands);
  }
  float daylight = smoothstep(0.005, 0.16, sun.y);
  float dawn = smoothstep(-0.095, 0.008, sun.y);
  float towardsSun = max(0.0, dot(ray, sun));
  vec3 zenith = mix(vec3(0.036, 0.035, 0.092), vec3(0.15, 0.18, 0.27), daylight);
  vec3 lower = mix(vec3(0.27, 0.095, 0.13), vec3(0.91, 0.30, 0.069), dawn);
  lower = mix(lower, vec3(0.78, 0.57, 0.30), daylight);
  lower = mix(lower, lower * vec3(0.71, 0.52, 0.78),
    (1.0 - pow(towardsSun, 3.2)) * dawn * (1.0 - 0.52 * daylight) * uSun);
  float horizon = exp(-y * mix(10.6, 7.4, daylight));
  vec3 color = mix(zenith, lower, horizon);
  color += vec3(0.11, 0.064, 0.10) * exp(-squared((y - 0.135) * 7.2)) * (1.0 - daylight);
  color += mix(vec3(0.27, 0.22, 0.12), vec3(0.20, 0.17, 0.11), daylight)
    * pow(towardsSun, mix(24.0, 15.0, daylight)) * (0.22 + 0.78 * dawn);
  color += vec3(0.16, 0.13, 0.064) * exp(-y * 39.0) * pow(towardsSun, 78.0) * dawn;

  if (uScene > 0.5 && uScene < 1.5) {
    return mix(vec3(0.014, 0.034, 0.090), vec3(0.07, 0.17, 0.28), exp(-y * 9.0));
  }
  if (uScene == 2.0) {
    return mix(vec3(0.025, 0.047, 0.16), vec3(0.26, 0.19, 0.36), exp(-y * 12.0));
  }
  return color;
}

vec2 cloudPoint(vec3 ray, float altitude) {
  return ray.xz * (altitude / (max(ray.y, 0.0) + 0.038)) * vec2(1.0, 1.18)
    + vec2(32.1, 16.7) + vec2(0.012, -0.008) * uClock;
}

float cloudField(vec2 p) {
  vec2 warp = vec2(noise2(p * 0.42 + 5.1), noise2(p * 0.42 + 49.2)) - 0.5;
  return cloudNoise(p + warp * 1.02);
}

float cloudThreshold() {
  return mix(0.72, 0.35, pow(clamp(uCloud, 0.0, 1.0), 0.68));
}

vec3 reflectedSky(vec3 ray, vec3 sun) {
  vec3 color = atmosphere(ray, sun);
  if (uCloud <= 0.001 || uScene == 1.0) return color;
  float density = cloudField(cloudPoint(ray, 0.72));
  float body = smoothstep(cloudThreshold() - 0.080, cloudThreshold() + 0.23, density);
  vec3 cloudBase = mix(vec3(0.24, 0.11, 0.15), vec3(0.37, 0.31, 0.30), smoothstep(0.0, 0.11, sun.y));
  if (uScene == 2.0) cloudBase = vec3(0.09, 0.11, 0.24);
  return mix(color, cloudBase, body * smoothstep(0.015, 0.10, ray.y) * 0.54);
}

vec3 cloudscape(vec3 ray, vec3 sun, vec3 color) {
  if (uCloud <= 0.001 || ray.y <= 0.006) return color;
  float daylight = smoothstep(0.016, 0.136, sun.y);
  float morning = smoothstep(-0.09, -0.005, sun.y);
  float threshold = cloudThreshold();
  vec2 p = cloudPoint(ray, 1.17);
  vec2 windward = normalize(sun.xz + vec2(0.001, 0.0));
  float aperture = exp(-squared((ray.x - 0.36) * 4.8) - squared((ray.y - 0.335) * 6.8));
  float density = cloudField(p) - 0.105 * aperture;
  float litDensity = cloudField(p + windward * 0.15 + vec2(0.045, -0.025));
  float heightMask = smoothstep(0.009, 0.072, ray.y);
  float far = cloudField(cloudPoint(ray, 1.75) * vec2(0.45, 1.51) + 14.0);
  float farAlpha = smoothstep(threshold - 0.058, threshold + 0.11, far)
    * smoothstep(0.006, 0.044, ray.y) * 0.80;
  float sunAngle = max(0.0, dot(ray, sun));
  float scatter = pow(sunAngle, 12.0) * exp(-max(ray.y - 0.065, 0.0) * 2.6);
  vec3 thin = mix(vec3(0.30, 0.13, 0.21), vec3(0.46, 0.39, 0.35), daylight);
  thin += mix(vec3(1.28, 0.84, 0.48), vec3(1.38, 1.10, 0.82), daylight) * scatter * morning;
  if (uScene == 2.0) thin = vec3(0.12, 0.14, 0.31);
  color = mix(color, thin, farAlpha);

  float alpha = smoothstep(threshold - 0.032, threshold + 0.063, density) * heightMask;
  float thickness = smoothstep(threshold + 0.015, threshold + 0.15, density);
  float rim = 1.0 - smoothstep(0.023, 0.162, density - threshold);
  float light = clamp(0.31 + (density - litDensity) * 13.6, 0.0, 1.0);
  float warm = (0.36 + 0.64 * scatter) * morning;
  vec3 shadow = mix(vec3(0.095, 0.046, 0.09), vec3(0.12, 0.13, 0.18), daylight);
  vec3 body = mix(vec3(0.49, 0.085, 0.062), vec3(0.39, 0.30, 0.28), daylight);
  vec3 edge = mix(vec3(1.44, 0.44, 0.17), vec3(1.53, 1.15, 0.77), daylight);
  if (uScene == 2.0) {
    shadow = vec3(0.027, 0.041, 0.117);
    body = vec3(0.07, 0.115, 0.27);
    edge = vec3(0.20, 0.25, 0.48);
  }
  vec3 clouds = mix(shadow, body, (0.19 + 0.81 * light) * (1.0 - 0.57 * thickness));
  clouds += edge * warm * (0.62 * light * (1.0 - 0.52 * thickness) + 0.55 * rim);
  clouds += edge * rim * scatter * 0.12;
  return mix(color, clouds, alpha);
}

vec3 aurora(vec3 ray) {
  vec3 color = vec3(0.0);
  if (ray.y <= 0.015) return color;
  float angle = atan(ray.x, ray.z);
  for (int i = 0; i < 3; i++) {
    float layer = float(i);
    float x = angle * (1.0 + layer * 0.17) + layer * 1.8 + 0.018 * uClock;
    float base = 0.11 + layer * 0.145 + 0.045 * sin(5.0 * x) + 0.023 * sin(11.0 * x + layer);
    float height = ray.y - base;
    float veil = smoothstep(-0.012, 0.033, height) * exp(-max(height, 0.0) * (10.0 - layer));
    float folds = pow(noise2(vec2(x * 39.0, layer * 9.1)), 1.6);
    float fibers = 0.45 + 0.55 * noise2(vec2(x * 174.0, layer * 23.7));
    float width = 0.24 + 0.76 * noise2(vec2(x * 5.1, layer + 3.2));
    vec3 light = mix(vec3(0.08, 0.89, 0.49), vec3(0.17, 0.33, 0.84), smoothstep(0.03, 0.27, height));
    color += light * veil * folds * fibers * width * (1.34 - layer * 0.23);
  }
  return color;
}

vec3 stars(vec3 ray) {
  vec2 p = vec2(atan(ray.x, ray.z), asin(ray.y)) * 160.0;
  vec2 cell = floor(p);
  float point = noise2(cell + 22.5);
  float glimmer = smoothstep(0.975, 0.999, point);
  float core = 1.0 - smoothstep(0.035, 0.14, length(fract(p) - 0.5));
  return vec3(0.58, 0.73, 1.0) * glimmer * core * smoothstep(0.08, 0.28, ray.y);
}

vec3 sunDisk(vec3 color, vec3 ray, vec3 sun) {
  float radius = length(ray - sun);
  float edge = 0.55 / uResolution.y;
  float disc = 1.0 - smoothstep(0.0128 - edge, 0.0128 + edge, radius);
  vec3 glow = vec3(1.0, 0.61, 0.23);
  float halo = 0.00043 / (radius * radius + 0.00039) * exp(-radius * 3.0);
  float isolines = 0.0;
  if (uStage == 2.0) {
    float ring = abs(fract(radius / 0.041 + 0.5) - 0.5) * 0.041;
    isolines = 0.30 * (1.0 - smoothstep(0.0, 1.6 * edge, ring))
      * smoothstep(0.022, 0.047, radius) * (1.0 - smoothstep(0.12, 0.22, radius))
      * (1.0 - smoothstep(0.48, 0.88, uBuild));
  }
  return color + (glow * (halo + isolines) + vec3(1.46, 1.35, 0.95) * disc) * uSun;
}

vec2 skyOffset(vec3 ray, vec3 target) {
  vec3 right = normalize(cross(vec3(0.0, 1.0, 0.0), target));
  vec3 up = cross(target, right);
  return vec2(dot(ray, right), dot(ray, up));
}

vec3 saturn(vec3 color, vec3 ray) {
  vec3 target = normalize(vec3(-0.19, 0.26, 1.0));
  if (dot(ray, target) < 0.94) return color;
  vec2 p = skyOffset(ray, target);
  float radius = length(p);
  vec2 plane = mat2(0.91, -0.414, 0.414, 0.91) * p;
  float ring = length(vec2(plane.x, plane.y * 4.7));
  float band = smoothstep(0.116, 0.120, ring) * (1.0 - smoothstep(0.223, 0.229, ring));
  band *= (0.40 + 0.60 * noise2(vec2(ring * 314.0, 12.5)));
  band *= 1.0 - 0.68 * exp(-squared((ring - 0.185) * 360.0));
  vec3 ice = vec3(0.69, 0.60, 0.56);
  color = mix(color, ice, band * 0.48);
  float sphere = 1.0 - smoothstep(0.089, 0.091, radius);
  vec3 normal = vec3(p / 0.09, sqrt(max(0.0, 1.0 - radius * radius / 0.0081)));
  float lit = 0.28 + 0.72 * max(0.0, dot(normal, normalize(vec3(0.55, -0.67, 0.59))));
  float stripes = 0.84 + 0.16 * sin((plane.y + normal.z * 0.017) * 195.0);
  color = mix(color, vec3(0.69, 0.49, 0.35) * lit * stripes, sphere * 0.50);
  return mix(color, ice, band * smoothstep(-0.006, 0.008, -plane.y) * sphere * 0.63);
}

vec3 blackHole(vec3 color, vec3 ray, vec3 center) {
  if (dot(ray, center) < 0.92) return color;
  vec2 p = skyOffset(ray, center);
  vec2 q = mat2(0.975, 0.222, -0.222, 0.975) * p;
  float r = length(p);
  float angle = atan(q.y, q.x);
  float flicker = 0.66 + 0.34 * noise2(vec2(angle * 9.0 + uClock * 0.45, r * 213.0));
  float halo = exp(-abs(r - 0.077) * 56.0) * 0.24;
  float arc = exp(-squared((r - 0.072) * 107.0)) * (0.47 + 0.36 * sin(angle + 0.64));
  float photonRing = exp(-squared((r - 0.064) * 416.0)) * 0.78;
  float shadow = 1.0 - smoothstep(0.059, 0.063, r);
  float discWidth = (0.007 + 0.012 * exp(-abs(q.x) * 8.0));
  float disc = exp(-squared(q.y / discWidth) - squared(q.x * 5.2));
  disc *= (0.63 + 0.37 * smoothstep(-0.19, 0.12, q.x)) * (0.58 + 0.42 * noise2(q * 101.0));
  vec3 fire = vec3(1.0, 0.56, 0.22);
  color *= 1.0 - shadow * 0.985;
  return color + fire * (halo + flicker * arc + disc * 1.8)
    + vec3(1.0, 0.93, 0.74) * (photonRing + 0.62 * exp(-squared(q.y * 200.0)) * disc);
}
`;
