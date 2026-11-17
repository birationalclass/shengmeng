export const isletSource = `
const float ISLET_SCALE = 0.78;
float isletHash(vec3 p) {
  p = fract(p * 0.1031);
  p += dot(p, p.zyx + 33.33);
  return fract((p.x + p.y) * p.z);
}

float isletNoise(vec3 p) {
  vec3 a = floor(p);
  vec3 f = fract(p);
  f = f * f * (3.0 - 2.0 * f);
  float x0 = mix(isletHash(a), isletHash(a + vec3(1.0, 0.0, 0.0)), f.x);
  float x1 = mix(isletHash(a + vec3(0.0, 1.0, 0.0)), isletHash(a + vec3(1.0, 1.0, 0.0)), f.x);
  float x2 = mix(isletHash(a + vec3(0.0, 0.0, 1.0)), isletHash(a + vec3(1.0, 0.0, 1.0)), f.x);
  float x3 = mix(isletHash(a + vec3(0.0, 1.0, 1.0)), isletHash(a + vec3(1.0, 1.0, 1.0)), f.x);
  return mix(mix(x0, x1, f.y), mix(x2, x3, f.y), f.z);
}

float isletBox(vec3 p, vec3 halfSize) {
  vec3 d = abs(p) - halfSize;
  return length(max(d, 0.0)) + min(0.0, max(d.x, max(d.y, d.z)));
}

float isletBoulder(vec3 p, vec3 center, vec3 radii, vec2 turn, float lean) {
  vec3 v = p - center;
  v.xz = mat2(turn.x, -turn.y, turn.y, turn.x) * v.xz;
  v.x += lean * v.y;
  v.z -= 0.15 * v.y;
  vec3 q = abs(v / radii);
  float rounded = mix(length(q), max(q.x, max(q.y, q.z)), 0.48);
  float bevel = dot(q, vec3(0.46, 0.68, 0.39));
  return (max(rounded, bevel) - 1.0) * min(radii.x, min(radii.y, radii.z));
}

vec3 isletHouseSpace(vec3 p) {
  vec3 q = p - vec3(12.50, 4.25, -10.25);
  q.xz = mat2(0.954, -0.30, 0.30, 0.954) * q.xz;
  return q;
}

vec2 isletShape(vec3 p) {
  float bed = isletBoulder(p, vec3(1.0, -2.4, 0.7), vec3(43.2, 4.95, 21.2), vec2(0.98, 0.20), 0.10);
  float rock = isletBoulder(p, vec3(-14.5, 2.7, 5.9), vec3(27.2, 7.0, 19.0), vec2(0.99, 0.12), -0.16);
  rock = min(rock, isletBoulder(p, vec3(-24.6, 5.2, -4.2), vec3(17.0, 11.7, 12.4), vec2(0.95, -0.31), 0.14));
  rock = min(rock, isletBoulder(p, vec3(-17.5, 11.3, 5.8), vec3(13.2, 10.0, 12.1), vec2(0.86, 0.51), -0.19));
  rock = min(rock, isletBoulder(p, vec3(-24.7, 16.6, 7.2), vec3(9.4, 7.1, 8.2), vec2(0.99, -0.14), -0.08));
  rock = min(rock, isletBoulder(p, vec3(-4.1, 4.0, 9.0), vec3(11.3, 9.7, 13.7), vec2(0.79, 0.61), 0.33));
  rock = min(rock, isletBoulder(p, vec3(13.0, 2.0, 7.5), vec3(18.8, 6.5, 14.3), vec2(0.87, -0.49), 0.02));
  rock = min(rock, isletBoulder(p, vec3(31.9, 0.1, 4.9), vec3(12.7, 4.2, 9.3), vec2(0.95, 0.31), -0.03));
  rock = min(rock, isletBoulder(p, vec3(-1.1, 0.8, -17.9), vec3(10.7, 3.6, 6.5), vec2(0.89, 0.46), -0.18));
  rock = min(rock, isletBoulder(p, vec3(-34.0, 0.8, -12.0), vec3(9.4, 4.8, 9.7), vec2(0.77, -0.64), 0.08));
  rock = min(rock, isletBoulder(p, vec3(11.9, 0.3, -11.6), vec3(12.0, 4.0, 10.9), vec2(1.0, 0.0), 0.03));

  if (rock < 3.0) {
    float weathering = isletNoise(p * 0.18 + 19.3);
    vec3 bedding = vec3(p.x * 0.24, (p.y + 0.13 * p.x - 0.13 * p.z) * 0.62, p.z * 0.30);
    float block = isletNoise(bedding + weathering * 0.54);
    float jointNoise = isletNoise(vec3(p.x * 0.45, p.y * 0.10, p.z * 0.45) + 3.71);
    float grain = isletNoise(p * 0.91 + 8.4);
    float seams = smoothstep(0.52, 0.99, sin(bedding.y * 2.7 + weathering * 2.6));
    float joint = exp(-9.2 * abs(jointNoise - 0.47)) * smoothstep(0.27, 0.71, block);
    rock += (weathering - 0.5) * 2.35 + (block - 0.5) * 1.20 + (grain - 0.5) * 0.40;
    rock += 0.51 * joint + 0.31 * seams * smoothstep(0.33, 0.69, block);
  }
  vec2 hit = rock < bed ? vec2(rock, 1.0) : vec2(bed, 2.0);

  vec3 q = isletHouseSpace(p);
  if (max(abs(q.x), abs(q.z)) < 18.0 && abs(q.y - 3.2) < 13.0) {
    float slope = 7.3 - abs(q.x) * 0.44;
    float gable = max(max(abs(q.x) - 6.35, abs(q.z) - 5.28), max(0.24 - q.y, (q.y - slope) * 0.91));
    float deck = isletBox(q - vec3(0.0, 0.32, -5.9), vec3(6.85, 0.19, 3.0));
    vec3 s = q;
    s.x = abs(s.x) - 5.7;
    float posts = isletBox(s - vec3(0.0, -0.72, -8.2), vec3(0.20, 1.19, 0.20));
    float timber = min(gable, min(deck, posts));
    float roof = max(max(abs(q.x) - 7.32, abs(q.z) - 6.2), abs(q.y - slope - 0.12) * 0.91 - 0.245);
    if (timber < hit.x) hit = vec2(timber, 3.0);
    if (roof < hit.x) hit = vec2(roof, 4.0);
  }
  return hit;
}

vec3 isletNormal(vec3 p) {
  vec2 e = vec2(0.13, -0.13);
  vec3 n = e.xyy * isletShape(p + e.xyy).x +
    e.yyx * isletShape(p + e.yyx).x +
    e.yxy * isletShape(p + e.yxy).x +
    e.xxx * isletShape(p + e.xxx).x;
  return normalize(n + vec3(0.0, 0.00002, 0.0));
}

float isletPanel(vec2 p, vec2 halfSize) {
  vec2 q = abs(p) / halfSize;
  return 1.0 - smoothstep(0.93, 1.06, max(q.x, q.y));
}

vec3 isletAlbedo(vec3 p, vec3 n, float material) {
  if (material < 2.5) {
    float eroded = isletNoise(p * 0.17 + 14.7);
    float small = isletNoise(p * 1.85 + 1.43);
    float fracture = max(0.0, sin((p.y + 0.12 * p.x - 0.08 * p.z) * 2.25 + eroded * 2.1));
    vec3 limestone = mix(vec3(0.17, 0.146, 0.115), vec3(0.55, 0.49, 0.35), smoothstep(0.25, 0.76, eroded));
    limestone *= 0.67 + 0.24 * small + 0.21 * smoothstep(0.08, 0.63, n.y) - 0.11 * pow(fracture, 10.0);
    float moss = smoothstep(0.58, 0.82, eroded) * smoothstep(0.13, 0.55, n.y) * 0.48;
    limestone = mix(limestone, vec3(0.20, 0.235, 0.13), moss);
    vec3 sand = mix(vec3(0.35, 0.33, 0.24), vec3(0.56, 0.51, 0.37), eroded);
    vec3 rock = material < 1.5 ? limestone : sand;
    float dry = smoothstep(-0.09, 1.78, p.y + (small - 0.5) * 0.63);
    return rock * mix(vec3(0.49, 0.58, 0.59), vec3(1.0), dry);
  }

  vec3 q = isletHouseSpace(p);
  if (material > 3.5) {
    float seam = smoothstep(0.39, 0.50, abs(fract(q.z * 1.10) - 0.5));
    float board = isletHash(vec3(floor(q.z * 1.10), 4.6, 1.0));
    float texture = isletNoise(vec3(q.x * 0.34, q.y * 0.44, q.z * 3.5));
    float trim = max(smoothstep(5.93, 6.19, abs(q.z)), smoothstep(7.00, 7.30, abs(q.x)));
    vec3 roof = mix(vec3(0.40, 0.20, 0.046), vec3(0.96, 0.68, 0.28), 0.46 + 0.34 * board + 0.12 * texture);
    return roof * (1.00 - seam * 0.26 - trim * 0.51);
  }
  float across = mix(q.x, q.z, smoothstep(0.33, 0.67, abs(n.x)));
  float wood = isletNoise(vec3(across * 0.51, q.y * 5.80, q.z * 0.12));
  float seam = smoothstep(0.41, 0.50, abs(fract(q.y * 2.15) - 0.5));
  vec3 timber = mix(vec3(0.058, 0.027, 0.012), vec3(0.22, 0.105, 0.042), wood) * (1.0 - seam * 0.48);
  float front = 1.0 - smoothstep(-5.31, -5.12, q.z);
  vec2 doorAt = vec2(q.x - 0.39, q.y - 1.78);
  vec2 windowAt = vec2(abs(q.x - 0.10) - 3.68, q.y - 2.81);
  float frames = max(isletPanel(doorAt, vec2(1.04, 1.53)), isletPanel(windowAt, vec2(0.79, 0.75)));
  float panes = max(isletPanel(doorAt, vec2(0.88, 1.38)), isletPanel(windowAt, vec2(0.63, 0.58)));
  timber = mix(timber, vec3(0.30, 0.17, 0.083), frames * front);
  timber = mix(timber, vec3(0.025, 0.019, 0.014), panes * front);
  return timber;
}

vec4 traceIslet(vec3 eye, vec3 ray, vec3 origin, vec3 sun, vec3 sunColor, float groundShade) {
  vec3 eyeMeters = (eye - origin) * (1000.0 / ISLET_SCALE);
  vec3 toCenter = eyeMeters - vec3(0.0, 5.0, 0.0);
  float b = dot(toCenter, ray);
  float discriminant = b * b - dot(toCenter, toCenter) + 55.0 * 55.0;
  if (discriminant < 0.0) return vec4(0.0, 0.0, 0.0, 180.0);
  float root = sqrt(discriminant);
  float distanceMeters = max(0.0, -b - root);
  float farMeters = -b + root;
  if (abs(ray.y) > 0.0001) {
    vec2 verticalRange = (vec2(-0.6, 28.0) - eyeMeters.y) / ray.y;
    distanceMeters = max(distanceMeters, min(verticalRange.x, verticalRange.y));
    farMeters = min(farMeters, max(verticalRange.x, verticalRange.y));
  } else if (eyeMeters.y < -0.6 || eyeMeters.y > 28.0) {
    return vec4(0.0, 0.0, 0.0, 180.0);
  }
  for (int i = 0; i < 54; ++i) {
    if (distanceMeters > farMeters) break;
    vec3 p = eyeMeters + ray * distanceMeters;
    vec2 hit = isletShape(p);
    if (hit.x < 0.104) {
      vec3 n = isletNormal(p);
      float sky = smoothstep(-0.03, 0.32, sun.y);
      float sunVisibility = clamp(groundShade, 0.0, 1.0);
      float cosine = max(0.0, dot(n, sun));
      float occlusion = clamp(isletShape(p + n * 0.79).x * 1.35 + 0.17, 0.27, 1.0);
      float localShadow = 1.0;
      if (cosine > 0.025 && sunVisibility > 0.04) {
        float stepMeters = 0.83;
        for (int s = 0; s < 4; ++s) {
          float d = isletShape(p + n * 0.31 + sun * stepMeters).x;
          localShadow = min(localShadow, smoothstep(-0.07, 0.41 * stepMeters, d));
          stepMeters *= 2.13;
        }
      }
      vec3 ambient = mix(vec3(0.095, 0.10, 0.13), vec3(0.29, 0.36, 0.42), sky);
      ambient *= (0.55 + 0.45 * max(n.y, 0.0)) * occlusion;
      vec3 reflectedWater = vec3(0.024, 0.063, 0.062) * sky * exp(-max(0.0, p.y) * 0.26) * (1.0 - max(n.y, 0.0));
      vec3 direct = sunColor * cosine * sunVisibility * mix(0.29, 0.91, localShadow);
      vec3 lit = isletAlbedo(p, n, hit.y) * (ambient + reflectedWater + direct);
      return vec4(max(lit, vec3(0.0)), distanceMeters * (0.001 * ISLET_SCALE));
    }
    distanceMeters += max(0.074, hit.x * 0.79);
  }
  return vec4(0.0, 0.0, 0.0, 180.0);
}
`;
