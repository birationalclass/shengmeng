/* Mineral point sprites for the course opening. No textures or external assets.
 * A particle keeps its seed, colour, grain type and trajectory across every scene.
 * localOffset mirrors the vertex shader before camera fitting, for authoring checks.
 */
(() => {
  'use strict';
  const vertex = `precision highp float;
    attribute vec2 start;
    attribute vec2 finish;
    attribute vec4 grain;
    uniform float progress;
    uniform float aspect;
    uniform float dpr;
    uniform float time;
    uniform float colorAmount;
    uniform mediump float complexity;
    uniform mediump float depth;
    uniform float wander;
    varying mediump vec3 color;
    varying mediump float opacity;
    varying mediump vec4 material;

    vec2 localWander(vec2 p) {
      float a = time * .33;
      vec2 eddy = vec2(
        sin(p.y * 15. + a) * cos(p.x * 9. - time * .17),
        -sin(p.x * 15. - time * .28) * cos(p.y * 9. + time * .21)
      );
      vec2 drift = vec2(
        sin(time * (.42 + .45 * grain.z) + grain.x * 6.28318530718) *
          cos(time * .17 + grain.y * 6.28318530718),
        cos(time * (.36 + .40 * grain.w) + grain.y * 6.28318530718) *
          sin(time * .19 + grain.x * 6.28318530718)
      );
      vec2 fine = vec2(
        sin(time * 1.31 + grain.z * 6.28318530718),
        cos(time * 1.13 + grain.w * 6.28318530718)
      );
      // The sum has component magnitude <= 1; its vector length is < .025.
      return .0176 * wander * (.30 * eddy + .50 * drift + .20 * fine);
    }

    vec3 mineral(float selector) {
      if (selector < .26) return vec3(.20, .52, .38);  // malachite
      if (selector < .49) return vec3(.24, .40, .70);  // lapis blue
      if (selector < .73) return vec3(.83, .43, .25);  // copper
      return vec3(.90, .86, .72);                     // pale quartz
    }

    void main() {
      float t = progress;
      float e = t * t * t * (t * (t * 6. - 15.) + 10.);
      vec2 delta = finish - start;
      float arch = sin(3.14159265359 * e);
      vec2 p = mix(start, finish, e) + vec2(-delta.y, delta.x) * arch * .28;
      float dist = length(delta);
      p += vec2(sin(grain.x * 19. + e * 6.283), cos(grain.y * 23. - e * 6.283)) *
        arch * min(.022, dist * .16);
      p += localWander(p);
      float fit = min(.68, aspect * .84);
      p *= fit;
      p.y += mix(.05, .20, smoothstep(.8, 1.3, aspect));
      p.x /= aspect;
      gl_Position = vec4(p, 0., 1.);

      // Most grains stay fine; rare fragments provide tactile scale contrast.
      float variedSize = .64 + 1.02 * grain.y;
      if (grain.z > .64) variedSize = 1.50 + .96 * grain.y;
      if (grain.z > .94) variedSize = 2.78 + 1.18 * grain.y;
      float size = mix(1.45 + .16 * grain.z, variedSize, complexity);
      gl_PointSize = size * mix(1., 1.16, depth) * dpr;

      float light = .74 + .26 * clamp(1. - length(p - vec2(-.35, .48)) * .5, 0., 1.);
      vec3 gold = mix(vec3(.46, .33, .16), vec3(.91, .77, .49), grain.w);
      gold = mix(gold, vec3(.99, .91, .74), pow(grain.y, 18.) * .55);
      float selector = fract(grain.y * 17.17 + grain.z * 31.31);
      vec3 tint = mineral(selector) * (.73 + .27 * grain.w);
      // At full strength at least 28 percent of the grains remain gold.
      float coloured = 1. - smoothstep(colorAmount * .72 - .012, colorAmount * .72, grain.x);
      coloured *= step(.001, colorAmount);
      color = mix(gold, tint, coloured) * light;
      opacity = (.65 + .30 * grain.x) * (1. - complexity * step(.94, grain.z) * .10);
      material = grain;
    }`;

  const fragment = `precision mediump float;
    uniform mediump float depth;
    uniform mediump float complexity;
    varying mediump vec3 color;
    varying mediump float opacity;
    varying mediump vec4 material;
    void main() {
      vec2 p = gl_PointCoord * 2. - 1.;
      float angle = material.x * 6.28318530718;
      float c = cos(angle), s = sin(angle);
      vec2 turned = vec2(c * p.x + s * p.y, -s * p.x + c * p.y);
      float axis = .72 + .28 * material.y;
      vec2 shaped = vec2(turned.x / axis, turned.y);
      float polar = atan(shaped.y, shaped.x + .00001);
      float outline = .90 + .055 * sin(polar * 5. + material.x * 6.28318530718) +
        .035 * sin(polar * 3. + material.y * 10.);
      float character = max(depth, complexity * .7);
      vec2 q = mix(p * vec2(1., .84 + material.z * .22), shaped / outline, character);
      float r = length(q);
      if (r > 1.) discard;

      float flatAlpha = 1. - smoothstep(.25, 1., r);
      float flatShade = .74 + .26 * clamp(.5 - p.x * .5 + p.y * .2, 0., 1.);
      vec3 flatColor = color * flatShade;

      // Convex ellipsoid normals, with subtle irregularities for chipped grains.
      vec2 nxy = vec2(q.x / axis, q.y);
      nxy += .075 * vec2(sin(q.y * 6. + material.x * 6.), cos(q.x * 7. + material.y * 6.)) * r;
      nxy = vec2(c * nxy.x - s * nxy.y, s * nxy.x + c * nxy.y);
      vec3 n = normalize(vec3(nxy, sqrt(max(.008, 1. - r * r))));
      vec3 lamp = normalize(vec3(-.52, -.64, .68));
      vec3 halfway = normalize(lamp + vec3(0., 0., 1.));
      float diffuse = max(0., dot(n, lamp));
      float specular = pow(max(0., dot(n, halfway)), 20. + 28. * material.z);
      float rim = 1. - .30 * smoothstep(.64, 1., r);
      vec3 solidColor = color * (.25 + .91 * diffuse) * rim;
      solidColor += vec3(1., .94, .79) * specular * (.20 + .18 * material.y);
      float solidAlpha = 1. - smoothstep(.82, 1., r);
      gl_FragColor = vec4(mix(flatColor, solidColor, depth),
        mix(flatAlpha, solidAlpha, depth) * opacity);
    }`;

  function localOffset(x, y, g0, g1, g2, g3, time, amount) {
    const tau = 6.28318530718;
    const eddyX = Math.sin(y * 15 + time * .33) * Math.cos(x * 9 - time * .17);
    const eddyY = -Math.sin(x * 15 - time * .28) * Math.cos(y * 9 + time * .21);
    const driftX = Math.sin(time * (.42 + .45 * g2) + g0 * tau) * Math.cos(time * .17 + g1 * tau);
    const driftY = Math.cos(time * (.36 + .40 * g3) + g1 * tau) * Math.sin(time * .19 + g0 * tau);
    const fineX = Math.sin(time * 1.31 + g2 * tau);
    const fineY = Math.cos(time * 1.13 + g3 * tau);
    return [
      .0176 * amount * (.30 * eddyX + .50 * driftX + .20 * fineX),
      .0176 * amount * (.30 * eddyY + .50 * driftY + .20 * fineY)
    ];
  }

  window.CourseOpeningMaterials = Object.freeze({ vertex, fragment, localOffset });
})();
