// Independent GLSL implementation of the light paths described in AshenOneArt's
// HPWater BSDF documentation:
// https://github.com/AshenOneArt/HPWater/wiki/BSDF%E2%80%90Model
export const opticsSource = `
const float WATER_OPTICS_PI = 3.14159265359;
const float WATER_OPTICS_IOR_RATIO = 1.0 / 1.333;

vec3 waterOpticalAbsorption(float clarity) {
  return mix(vec3(0.68, 0.64, 1.23), vec3(0.68, 0.115, 0.090),
    smoothstep(0.0, 1.0, clarity));
}

vec3 waterOpticalScattering(float clarity) {
  return mix(vec3(0.40, 0.40, 0.105), vec3(0.038, 0.095, 0.145),
    smoothstep(0.0, 1.0, clarity));
}

// Depth is a distance along the refracted ray, in metres.
vec3 waterTransmittance(float depth, float clarity) {
  vec3 extinction = waterOpticalAbsorption(clarity) + waterOpticalScattering(clarity);
  return exp(-extinction * max(depth, 0.0));
}

float waterOpticalFresnel(float cosine) {
  float complement = 1.0 - clamp(cosine, 0.0, 1.0);
  float square = complement * complement;
  return 0.02037 + 0.97963 * square * square * complement;
}

float waterOpticalHG(float cosine, float anisotropy, float angularSpread) {
  float narrowness = 1.0 - anisotropy;
  float denominator = narrowness * narrowness
    + 2.0 * anisotropy * (1.0 - clamp(cosine, -1.0, 1.0)) + angularSpread;
  float reciprocalRoot = inversesqrt(denominator);
  return (1.0 - anisotropy * anisotropy) * reciprocalRoot / denominator;
}

vec3 waterOpticalPhase(float cosine, float spread) {
  float forwardPhase = waterOpticalHG(cosine, 0.8, spread);
  vec3 rayleigh = vec3(0.31, 0.59, 1.0) * (0.75 * (1.0 + cosine * cosine));
  return mix(vec3(forwardPhase), rayleigh, 0.05);
}

float waterOpticalGGX(vec3 N, vec3 V, vec3 L, float roughness) {
  float normalView = dot(N, V);
  float normalLight = dot(N, L);
  if (normalLight <= 0.0 || normalView <= 0.0) return 0.0;

  vec3 H = normalize(V + L);
  float normalHalf = max(dot(N, H), 0.0);
  // Minimum width represents the finite sun disc and keeps a moving highlight stable.
  float alpha = max(0.025, roughness * roughness);
  float alpha2 = alpha * alpha;
  float ggxDenominator = 1.0 + (alpha2 - 1.0) * normalHalf * normalHalf;
  float distribution = alpha2 / (WATER_OPTICS_PI * ggxDenominator * ggxDenominator);
  float masking = normalLight * sqrt(mix(alpha2, 1.0, normalView * normalView))
    + normalView * sqrt(mix(alpha2, 1.0, normalLight * normalLight));
  float irradiance = distribution * normalLight * waterOpticalFresnel(dot(V, H))
    / max(2.0 * masking, 0.0001);
  return irradiance / (1.0 + irradiance * 0.14);
}

vec3 waterVolumeScattering(float depth, float entryPath, float phaseCosine,
  vec3 extinction, vec3 albedo, vec3 lightRadiance, vec3 ambientRadiance) {
  vec3 phase = waterOpticalPhase(phaseCosine, 0.028);
  vec3 scattering = vec3(0.0);
  vec3 viewTransmittance = vec3(1.0);

  // Integrate six exponential intervals from the surface toward the bed.
  // Each interval integrates extinction on the view segment exactly.
  float boundaryFactor = 1.0;
  for (int i = 0; i < 6; ++i) {
    float begin = depth * (boundaryFactor - 1.0) / 7.0;
    boundaryFactor *= 1.41421356237;
    float end = depth * (boundaryFactor - 1.0) / 7.0;
    float sampleDistance = 0.5 * (begin + end);
    vec3 segmentTransmittance = exp(-extinction * (end - begin));
    vec3 lightTransmittance = exp(-extinction * (sampleDistance * entryPath));
    vec3 intervalPhase = mix(phase, vec3(1.0),
      clamp(vec3(1.0) - lightTransmittance * viewTransmittance, 0.16, 0.85));
    vec3 incident = lightRadiance * lightTransmittance * intervalPhase * 0.26
      + ambientRadiance;
    scattering += incident * albedo * (1.0 - segmentTransmittance) * viewTransmittance;
    viewTransmittance *= segmentTransmittance;
  }
  return scattering;
}

// N faces the air and V/L point toward the eye and main light. Backgrounds
// and light radiance are scene-linear, without this interface's Fresnel or
// extinction. Thickness is normalized: 0 at crest edges, 1 at full depth.
vec3 waterOptics(vec3 N, vec3 V, vec3 L, vec3 reflectedEnvironment,
  vec3 refractedEnvironment, float thickness, float depth, float foam,
  float clarity, float roughness, int viewMode, vec3 lightRadiance) {
  float normalLight = clamp(dot(N, L), -1.0, 1.0);
  float normalView = max(dot(N, V), 0.0);
  float entry = max(normalLight, 0.0);
  float exitReflectance = waterOpticalFresnel(normalView);
  float exitTransmission = 1.0 - exitReflectance;
  float rough = clamp(roughness, 0.025, 1.0);
  float path = clamp(depth, 0.0, 100.0);
  float crest = clamp(thickness, 0.0, 1.0);
  vec3 absorption = waterOpticalAbsorption(clarity);
  vec3 particles = waterOpticalScattering(clarity);
  vec3 extinction = absorption + particles;
  vec3 albedo = particles / extinction;

  vec3 reflection = reflectedEnvironment * exitReflectance
    + lightRadiance * waterOpticalGGX(N, V, L, rough);
  if (viewMode == 4) return reflection;
  vec3 bedTransmittance = exp(-extinction * path);
  vec3 refraction = refractedEnvironment * bedTransmittance * exitTransmission;
  if (viewMode == 5) return refraction;

  vec3 intoWater = refract(-V, N, WATER_OPTICS_IOR_RATIO);
  vec3 sunInWater = refract(-L, vec3(0.0, 1.0, 0.0), WATER_OPTICS_IOR_RATIO);
  float entryPath = max(-intoWater.y, 0.04) / max(-sunInWater.y, 0.25);
  float phaseCosine = clamp(dot(-L, V), -1.0, 1.0);
  vec3 skyFill = min(reflectedEnvironment, vec3(1.4)) * 0.14;
  vec3 volume = waterVolumeScattering(path, entryPath, phaseCosine,
    extinction, albedo, lightRadiance, skyFill);
  // The refracted bed also illuminates the nearby water column.
  volume += refractedEnvironment * bedTransmittance * particles * min(path, 7.0) * 0.22;
  vec3 volumePath = volume * (entry * (1.0 - waterOpticalFresnel(entry))) * exitTransmission;
  if (viewMode == 1) return volumePath;

  // Grazing and rear illumination scatter in the short water layer. Optical
  // depth blends the linear path with a curved continuation into deep water.
  float opticalDensity = dot(extinction, vec3(0.2126, 0.7152, 0.0722));
  float straightPath = 2.3 * crest;
  float curvedPath = straightPath * crest * (1.0 + 2.0 * opticalDensity);
  float layerPath = min(path, mix(straightPath, curvedPath,
    clamp(0.40 * straightPath * opticalDensity, 0.0, 1.0)));
  vec3 layerTransmittance = exp(-extinction * layerPath);
  float layerWeight = 1.0 - dot(layerTransmittance, vec3(0.2126, 0.7152, 0.0722));
  vec3 phase = waterOpticalPhase(phaseCosine, 0.035 + 0.04 * rough);
  vec3 layerRadiance = (lightRadiance * phase * 0.16 + skyFill) * albedo
    * (1.0 - layerTransmittance);
  vec3 thinPath = mix(volume, layerRadiance, layerWeight)
    * (1.0 - entry) * exitTransmission;
  if (viewMode == 2) return thinPath;

  // The strongest forward lobe is broadened by the finite emitter and
  // unresolved ripple normals so it can remain visible between raster samples.
  float backProjection = max(-normalLight, 0.0);
  float backPhase = waterOpticalHG(phaseCosine, 0.998, 0.003 + 0.012 * rough);
  float rearPath = min(path, crest * 1.7 / (0.35 + backProjection));
  vec3 backPath = lightRadiance * exp(-extinction * rearPath)
    * (0.30 * backPhase * backProjection * exitTransmission);
  if (viewMode == 3) return backPath;

  vec3 water = reflection + refraction + volumePath + thinPath + backPath;
  vec3 foamLight = vec3(0.71, 0.77, 0.72)
    * (vec3(0.23) + max(skyFill, vec3(0.03)) + lightRadiance * (0.20 + 0.19 * entry));
  return mix(water, foamLight, clamp(foam, 0.0, 1.0) * 0.82);
}

vec3 waterOptics(vec3 N, vec3 V, vec3 L, vec3 reflectedEnvironment,
  vec3 refractedEnvironment, float thickness, float depth, float foam,
  float clarity, float roughness, int viewMode) {
  return waterOptics(N, V, L, reflectedEnvironment, refractedEnvironment,
    thickness, depth, foam, clarity, roughness, viewMode, vec3(2.35, 2.20, 1.95));
}
`;
