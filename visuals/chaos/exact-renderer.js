(() => {
  "use strict";

  const SETTINGS = Object.freeze({
    streamCount: 300,
    tailSegments: 360,
    streamSpacing: 827,
    worldRadius: 30,
    backgroundStars: 220,
    farCurveVisibility: 0.62,
    particleHaloScale: 2.56,
    particleCoreScale: 2.28,
    particleHaloOpacity: 0.10,
    particleGlowFalloff: 20,
    particleFarSize: 0.55,
    particleFarBrightness: 0.10,
    particleFarCoreBrightness: 0.35,
    particleFullBrightnessZoom: 10
  });

  const THEME_TRANSITION_SECONDS = 10;
  const THEME_COLOURS = Object.freeze([
    Object.freeze([0.24, 0.82, 1.00]),
    Object.freeze([0.16, 0.36, 1.00]),
    Object.freeze([0.62, 0.34, 1.00]),
    Object.freeze([1.00, 0.68, 0.18])
  ]);

  const FLOATS_PER_VERTEX = 7;
  const BYTES_PER_FLOAT = Float32Array.BYTES_PER_ELEMENT;

  function clamp(value, minimum, maximum) {
    return Math.min(maximum, Math.max(minimum, value));
  }

  function modulo(value, divisor) {
    return ((value % divisor) + divisor) % divisor;
  }

  function greatestCommonDivisor(left, right) {
    let a = Math.abs(Math.trunc(left));
    let b = Math.abs(Math.trunc(right));
    while (b !== 0) {
      const remainder = a % b;
      a = b;
      b = remainder;
    }
    return a;
  }

  function smootherstep(value) {
    const progress = clamp(value, 0, 1);
    return progress ** 3 * (progress * (progress * 6 - 15) + 10);
  }

  function percentile98(sortedValues) {
    if (sortedValues.length === 0) return Number.NaN;
    const position = (sortedValues.length - 1) * 0.98;
    const lower = Math.floor(position);
    const upper = Math.ceil(position);
    const fraction = position - lower;
    return sortedValues[lower] + (sortedValues[upper] - sortedValues[lower]) * fraction;
  }

  function flattenPoints(input) {
    const source = input && input.points ? input.points : input;
    if (ArrayBuffer.isView(source)) {
      if (source.length % 3 !== 0) throw new TypeError("Trajectory data must contain xyz triples.");
      return new Float32Array(source);
    }
    if (!Array.isArray(source)) throw new TypeError("setModel(points) expects a flat array or an array of xyz points.");
    if (source.length === 0) throw new TypeError("At least one trajectory point is required.");
    if (Array.isArray(source[0]) || ArrayBuffer.isView(source[0])) {
      const flattened = new Float32Array(source.length * 3);
      for (let index = 0; index < source.length; index += 1) {
        const point = source[index];
        if (!point || point.length < 3) throw new TypeError("Every trajectory point must contain x, y and z.");
        flattened[index * 3] = point[0];
        flattened[index * 3 + 1] = point[1];
        flattened[index * 3 + 2] = point[2];
      }
      return flattened;
    }
    if (source.length % 3 !== 0) throw new TypeError("Trajectory data must contain xyz triples.");
    return Float32Array.from(source);
  }

  // Python's random.Random integer seeding and random() implementation. Keeping
  // this local MT19937 makes the 220-star field match random.Random(20260712).
  class PythonRandom {
    constructor(seed) {
      this.state = new Uint32Array(624);
      this.index = 624;
      this.initializeByArray([Math.abs(Math.trunc(seed)) >>> 0]);
    }

    initialize(seed) {
      this.state[0] = seed >>> 0;
      for (let index = 1; index < 624; index += 1) {
        const previous = this.state[index - 1];
        this.state[index] = (Math.imul(previous ^ (previous >>> 30), 1812433253) + index) >>> 0;
      }
      this.index = 624;
    }

    initializeByArray(key) {
      this.initialize(19650218);
      let stateIndex = 1;
      let keyIndex = 0;
      let remaining = Math.max(624, key.length);
      while (remaining > 0) {
        const previous = this.state[stateIndex - 1];
        const mixed = Math.imul(previous ^ (previous >>> 30), 1664525);
        this.state[stateIndex] = ((this.state[stateIndex] ^ mixed) + key[keyIndex] + keyIndex) >>> 0;
        stateIndex += 1;
        keyIndex += 1;
        if (stateIndex >= 624) {
          this.state[0] = this.state[623];
          stateIndex = 1;
        }
        if (keyIndex >= key.length) keyIndex = 0;
        remaining -= 1;
      }
      remaining = 623;
      while (remaining > 0) {
        const previous = this.state[stateIndex - 1];
        const mixed = Math.imul(previous ^ (previous >>> 30), 1566083941);
        this.state[stateIndex] = ((this.state[stateIndex] ^ mixed) - stateIndex) >>> 0;
        stateIndex += 1;
        if (stateIndex >= 624) {
          this.state[0] = this.state[623];
          stateIndex = 1;
        }
        remaining -= 1;
      }
      this.state[0] = 0x80000000;
      this.index = 624;
    }

    twist() {
      const upperMask = 0x80000000;
      const lowerMask = 0x7fffffff;
      for (let index = 0; index < 624; index += 1) {
        const combined = (this.state[index] & upperMask) | (this.state[(index + 1) % 624] & lowerMask);
        let value = this.state[(index + 397) % 624] ^ (combined >>> 1);
        if (combined & 1) value ^= 0x9908b0df;
        this.state[index] = value >>> 0;
      }
      this.index = 0;
    }

    uint32() {
      if (this.index >= 624) this.twist();
      let value = this.state[this.index++];
      value ^= value >>> 11;
      value ^= (value << 7) & 0x9d2c5680;
      value ^= (value << 15) & 0xefc60000;
      value ^= value >>> 18;
      return value >>> 0;
    }

    random() {
      const high = this.uint32() >>> 5;
      const low = this.uint32() >>> 6;
      return (high * 67108864 + low) / 9007199254740992;
    }

    uniform(minimum, maximum) {
      return minimum + (maximum - minimum) * this.random();
    }
  }

  function shaderSources(webGL2) {
    const vertexBody = `
      precision highp float;
      ATTR vec3 aPosition;
      ATTR vec4 aColour;

      uniform float uYaw;
      uniform float uPitch;
      uniform float uWorldRadius;
      uniform float uAspect;
      uniform float uZoom;
      uniform float uPointScale;
      uniform float uOpacityScale;
      uniform float uFarVisibility;
      uniform vec3 uTarget;
      uniform vec2 uFraming;
      uniform vec2 uPixelOffset;

      VARY_OUT vec4 vColour;
      VARY_OUT float vDepthFade;

      void main() {
        vec3 localPosition = aPosition - uTarget;
        float cy = cos(uYaw);
        float sy = sin(uYaw);
        vec3 yawed = vec3(
          cy * localPosition.x + sy * localPosition.z,
          localPosition.y,
          -sy * localPosition.x + cy * localPosition.z
        );

        float cp = cos(uPitch);
        float sp = sin(uPitch);
        vec3 rotated = vec3(
          yawed.x,
          cp * yawed.y - sp * yawed.z,
          sp * yawed.y + cp * yawed.z
        );

        float cameraDistance = max(0.34, 2.70 + rotated.z / uWorldRadius);
        float perspective = 1.16 * uZoom / cameraDistance;
        gl_Position = vec4(
          rotated.x / uWorldRadius * perspective / uAspect,
          rotated.y / uWorldRadius * perspective,
          0.0,
          1.0
        );
        gl_Position.xy += uFraming + uPixelOffset;
        float depthPointScale = clamp(2.70 / cameraDistance, 0.52, 1.65);
        gl_PointSize = uPointScale * 6.0 * depthPointScale;
        vDepthFade = clamp(1.18 - 0.14 * cameraDistance, uFarVisibility, 1.0);
        vColour = vec4(aColour.rgb, aColour.a * uOpacityScale);
      }
    `;

    const trailBody = `
      precision highp float;
      VARY_IN vec4 vColour;
      VARY_IN float vDepthFade;
      FRAG_DECL
      void main() {
        FRAG_OUT = vec4(vColour.rgb * vDepthFade, vColour.a * vDepthFade);
      }
    `;

    const pointBody = `
      precision highp float;
      VARY_IN vec4 vColour;
      VARY_IN float vDepthFade;
      uniform float uGlowFalloff;
      uniform float uSolidCore;
      FRAG_DECL
      void main() {
        vec2 centered = gl_PointCoord * 2.0 - 1.0;
        float radiusSquared = dot(centered, centered);
        float glow = exp(-uGlowFalloff * radiusSquared);
        float solidCore = uSolidCore * (1.0 - smoothstep(0.14, 0.22, radiusSquared));
        float intensity = max(glow, solidCore);
        FRAG_OUT = vec4(
          vColour.rgb * intensity * vDepthFade,
          vColour.a * intensity * vDepthFade
        );
      }
    `;

    if (webGL2) {
      return {
        vertex: `#version 300 es\n${vertexBody}`
          .replaceAll("ATTR", "in")
          .replaceAll("VARY_OUT", "out"),
        trail: `#version 300 es\n${trailBody}`
          .replaceAll("VARY_IN", "in")
          .replace("FRAG_DECL", "out vec4 fragmentColour;")
          .replace("FRAG_OUT", "fragmentColour"),
        point: `#version 300 es\n${pointBody}`
          .replaceAll("VARY_IN", "in")
          .replace("FRAG_DECL", "out vec4 fragmentColour;")
          .replace("FRAG_OUT", "fragmentColour")
      };
    }

    return {
      vertex: vertexBody
        .replaceAll("ATTR", "attribute")
        .replaceAll("VARY_OUT", "varying"),
      trail: trailBody
        .replaceAll("VARY_IN", "varying")
        .replace("FRAG_DECL", "")
        .replace("FRAG_OUT", "gl_FragColor"),
      point: pointBody
        .replaceAll("VARY_IN", "varying")
        .replace("FRAG_DECL", "")
        .replace("FRAG_OUT", "gl_FragColor")
    };
  }

  class ChaosExactRenderer {
    constructor(canvas) {
      if (!(canvas instanceof HTMLCanvasElement)) {
        throw new TypeError("ChaosExactRenderer expects an HTMLCanvasElement.");
      }
      this.canvas = canvas;
      const options = {
        alpha: false,
        antialias: false,
        depth: false,
        stencil: false,
        premultipliedAlpha: false,
        preserveDrawingBuffer: false,
        powerPreference: "high-performance"
      };
      this.gl = canvas.getContext("webgl2", options)
        || canvas.getContext("webgl", options)
        || canvas.getContext("experimental-webgl", options);
      if (!this.gl) throw new Error("WebGL is required for the exact attractor renderer.");

      this.isWebGL2 = typeof WebGL2RenderingContext !== "undefined"
        && this.gl instanceof WebGL2RenderingContext;
      this.settings = SETTINGS;
      this.width = Math.max(1, canvas.width || 1);
      this.height = Math.max(1, canvas.height || 1);
      this.dpr = 1;
      this.points = null;
      this.pointCount = 0;
      this.orbitCenter = [0, 0, 0];
      this.displayScale = 1;
      this.phaseOffsets = new Int32Array(SETTINGS.streamCount);
      this.tailLengths = new Uint16Array(SETTINGS.streamCount);

      const sources = shaderSources(this.isWebGL2);
      this.trailProgram = this.buildProgram(sources.vertex, sources.trail);
      this.pointProgram = this.buildProgram(sources.vertex, sources.point);
      this.trailUniforms = this.uniformsFor(this.trailProgram);
      this.pointUniforms = this.uniformsFor(this.pointProgram);
      this.trailBuffer = this.gl.createBuffer();
      this.headBuffer = this.gl.createBuffer();
      this.starBuffer = this.gl.createBuffer();
      if (!this.trailBuffer || !this.headBuffer || !this.starBuffer) {
        throw new Error("WebGL could not allocate attractor buffers.");
      }

      const maximumTrailVertices = SETTINGS.streamCount * (SETTINGS.tailSegments * 2 + 2);
      this.trailScratch = new Float32Array(maximumTrailVertices * FLOATS_PER_VERTEX);
      this.headScratch = new Float32Array(SETTINGS.streamCount * FLOATS_PER_VERTEX);
      this.samplePositionScratch = new Float32Array(3);
      this.sampleTangentScratch = new Float32Array(3);
      this.starData = this.buildStars();
      this.gl.bindBuffer(this.gl.ARRAY_BUFFER, this.starBuffer);
      this.gl.bufferData(this.gl.ARRAY_BUFFER, this.starData, this.gl.STATIC_DRAW);
      this.gl.bindBuffer(this.gl.ARRAY_BUFFER, null);
    }

    get streamCount() {
      return SETTINGS.streamCount;
    }

    setModel(inputPoints) {
      const raw = flattenPoints(inputPoints);
      const count = raw.length / 3;
      if (count < 2) throw new TypeError("At least two trajectory points are required.");

      let meanX = 0;
      let meanY = 0;
      let meanZ = 0;
      for (let offset = 0; offset < raw.length; offset += 3) {
        const x = raw[offset];
        const y = raw[offset + 1];
        const z = raw[offset + 2];
        if (!Number.isFinite(x) || !Number.isFinite(y) || !Number.isFinite(z)) {
          throw new TypeError("Trajectory contains a non-finite coordinate.");
        }
        meanX += x;
        meanY += y;
        meanZ += z;
      }
      meanX /= count;
      meanY /= count;
      meanZ /= count;

      const radii = new Array(count);
      for (let index = 0; index < count; index += 1) {
        const offset = index * 3;
        radii[index] = Math.hypot(
          raw[offset] - meanX,
          raw[offset + 1] - meanY,
          raw[offset + 2] - meanZ
        );
      }
      radii.sort((left, right) => left - right);
      const robustRadius = percentile98(radii);
      if (!Number.isFinite(robustRadius) || robustRadius <= 1e-8) {
        throw new TypeError("Trajectory has no usable spatial extent.");
      }

      const displayScale = SETTINGS.worldRadius * 0.58 / robustRadius;
      const installed = new Float32Array(raw.length);
      for (let offset = 0; offset < raw.length; offset += 3) {
        installed[offset] = (raw[offset] - meanX) * displayScale;
        installed[offset + 1] = (raw[offset + 1] - meanY) * displayScale;
        installed[offset + 2] = (raw[offset + 2] - meanZ) * displayScale;
      }

      this.points = installed;
      this.pointCount = count;
      this.orbitCenter = [meanX, meanY, meanZ];
      this.displayScale = displayScale;

      let stride = SETTINGS.streamSpacing % count;
      while (greatestCommonDivisor(stride, count) !== 1) stride = (stride + 1) % count;
      const minimumTail = Math.max(2, Math.trunc(SETTINGS.tailSegments * 0.48));
      const variation = SETTINGS.tailSegments - minimumTail;
      for (let stream = 0; stream < SETTINGS.streamCount; stream += 1) {
        this.phaseOffsets[stream] = (stream * stride) % count;
        this.tailLengths[stream] = minimumTail
          + (stream * 97 + stream * stream * 11) % (variation + 1);
      }
      return this;
    }

    resize(width, height, dpr = window.devicePixelRatio || 1) {
      const cssWidth = Math.max(1, Number(width) || 1);
      const cssHeight = Math.max(1, Number(height) || 1);
      this.dpr = Math.max(0.25, Number(dpr) || 1);
      this.width = Math.max(1, Math.round(cssWidth * this.dpr));
      this.height = Math.max(1, Math.round(cssHeight * this.dpr));
      if (this.canvas.width !== this.width) this.canvas.width = this.width;
      if (this.canvas.height !== this.height) this.canvas.height = this.height;
      this.canvas.style.width = `${cssWidth}px`;
      this.canvas.style.height = `${cssHeight}px`;
      this.gl.viewport(0, 0, this.width, this.height);
      return this;
    }

    render(headPosition, animationSeconds, inputPose) {
      if (!this.points || this.pointCount === 0 || this.width <= 0 || this.height <= 0) return;
      const gl = this.gl;
      const pose = this.normalizedPose(inputPose);
      gl.viewport(0, 0, this.width, this.height);
      gl.clearColor(0.004, 0.008, 0.022, 1);
      gl.clear(gl.COLOR_BUFFER_BIT);
      gl.disable(gl.DEPTH_TEST);
      gl.disable(gl.CULL_FACE);
      gl.enable(gl.BLEND);
      gl.blendEquation(gl.FUNC_ADD);
      gl.blendFunc(gl.SRC_ALPHA, gl.ONE);

      const aspect = this.width / this.height;
      this.drawStars(aspect, pose);
      const counts = this.buildParticleVertices(headPosition, animationSeconds);

      gl.bindBuffer(gl.ARRAY_BUFFER, this.trailBuffer);
      gl.bufferData(
        gl.ARRAY_BUFFER,
        this.trailScratch.subarray(0, counts.trailFloats),
        gl.DYNAMIC_DRAW
      );
      gl.useProgram(this.trailProgram);
      this.bindVertexLayout(this.trailBuffer);
      for (const yPixels of [-1.4, 0, 1.4]) {
        for (const xPixels of [-1.4, 0, 1.4]) {
          this.setCamera(this.trailUniforms, aspect, pose, {
            pixelOffset: [2 * xPixels / this.width, 2 * yPixels / this.height],
            opacityScale: 0.14
          });
          gl.drawArrays(gl.LINES, 0, counts.trailVertices);
        }
      }

      gl.bindBuffer(gl.ARRAY_BUFFER, this.headBuffer);
      gl.bufferData(
        gl.ARRAY_BUFFER,
        this.headScratch.subarray(0, counts.headFloats),
        gl.DYNAMIC_DRAW
      );
      gl.useProgram(this.pointProgram);
      this.bindVertexLayout(this.headBuffer);

      const haloBrightness = this.particleBrightnessAtZoom(
        pose.zoom,
        SETTINGS.particleFarBrightness,
        SETTINGS.particleFullBrightnessZoom
      );
      const coreBrightness = this.particleBrightnessAtZoom(
        pose.zoom,
        SETTINGS.particleFarCoreBrightness,
        SETTINGS.particleFullBrightnessZoom
      );
      const particleSize = this.particleBrightnessAtZoom(
        pose.zoom,
        SETTINGS.particleFarSize,
        SETTINGS.particleFullBrightnessZoom
      );

      this.setCamera(this.pointUniforms, aspect, pose, {
        pointScale: SETTINGS.particleHaloScale * particleSize,
        opacityScale: SETTINGS.particleHaloOpacity * haloBrightness,
        glowFalloff: SETTINGS.particleGlowFalloff,
        solidCore: false
      });
      gl.drawArrays(gl.POINTS, 0, counts.headVertices);

      this.setCamera(this.pointUniforms, aspect, pose, {
        pointScale: SETTINGS.particleCoreScale * particleSize,
        opacityScale: coreBrightness,
        glowFalloff: SETTINGS.particleGlowFalloff,
        solidCore: true
      });
      gl.drawArrays(gl.POINTS, 0, counts.headVertices);
      gl.bindBuffer(gl.ARRAY_BUFFER, null);
    }

    particleSample(headPosition, stream) {
      if (!this.points || this.pointCount === 0) throw new Error("Call setModel(points) before particleSample().");
      if (!Number.isInteger(stream) || stream < 0 || stream >= SETTINGS.streamCount) {
        throw new RangeError("stream is outside the configured 300-particle range.");
      }
      const sample = this.sampleTrajectory(Number(headPosition) + this.phaseOffsets[stream]);
      const position = [sample.position[0], sample.position[1], sample.position[2]];
      const direction = [sample.tangent[0], sample.tangent[1], sample.tangent[2]];
      return { position, direction, tangent: direction };
    }

    destroy() {
      const gl = this.gl;
      if (this.trailBuffer) gl.deleteBuffer(this.trailBuffer);
      if (this.headBuffer) gl.deleteBuffer(this.headBuffer);
      if (this.starBuffer) gl.deleteBuffer(this.starBuffer);
      if (this.trailProgram) gl.deleteProgram(this.trailProgram);
      if (this.pointProgram) gl.deleteProgram(this.pointProgram);
      this.points = null;
      this.pointCount = 0;
    }

    normalizedPose(inputPose) {
      const pose = inputPose || {};
      const target = pose.target || [0, 0, 0];
      const framing = pose.framing || [0, 0];
      return {
        yaw: Number.isFinite(pose.yaw) ? pose.yaw : 0,
        pitch: Number.isFinite(pose.pitch) ? pose.pitch : 0,
        zoom: Number.isFinite(pose.zoom) ? pose.zoom : 1,
        target: [target[0] || 0, target[1] || 0, target[2] || 0],
        framing: [framing[0] || 0, framing[1] || 0]
      };
    }

    drawStars(aspect, pose) {
      const gl = this.gl;
      const starPose = {
        yaw: pose.yaw * 0.18,
        pitch: pose.pitch * 0.35,
        zoom: pose.zoom,
        target: [0, 0, 0],
        framing: [0, 0]
      };
      gl.useProgram(this.pointProgram);
      this.bindVertexLayout(this.starBuffer);
      this.setCamera(this.pointUniforms, aspect, starPose, { pointScale: 0.34 });
      gl.drawArrays(gl.POINTS, 0, SETTINGS.backgroundStars);
    }

    buildParticleVertices(headPosition, animationSeconds) {
      const pointCount = this.pointCount;
      const theme = this.themeAt(animationSeconds);
      let trailCursor = 0;
      let headCursor = 0;

      for (let stream = 0; stream < SETTINGS.streamCount; stream += 1) {
        const streamPosition = modulo(Number(headPosition) + this.phaseOffsets[stream], pointCount);
        const streamHead = Math.floor(streamPosition);
        const streamFraction = streamPosition - streamHead;
        const sampledHead = this.sampleTrajectory(
          streamPosition,
          this.samplePositionScratch,
          this.sampleTangentScratch
        ).position;
        const tailLength = this.tailLengths[stream];
        const boundaryFade = this.boundaryFade(streamPosition);

        if (streamFraction > 1e-8 && streamHead < pointCount - 1) {
          trailCursor = this.writeVertex(
            this.trailScratch,
            trailCursor,
            streamHead,
            theme[0], theme[1], theme[2],
            0.88 * boundaryFade
          );
          trailCursor = this.writeCoordinates(
            this.trailScratch,
            trailCursor,
            sampledHead,
            theme[0], theme[1], theme[2],
            0.88 * boundaryFade
          );
        }

        for (let age = tailLength; age >= 1; age -= 1) {
          const beforeIndex = modulo(streamHead - age, pointCount);
          if (beforeIndex === pointCount - 1) continue;
          const afterIndex = beforeIndex + 1;
          const life = 1 - (age - 1) / tailLength;
          const value = 0.20 + 0.80 * life;
          const alpha = (0.18 + 0.70 * life * life) * boundaryFade;
          const red = theme[0] * value;
          const green = theme[1] * value;
          const blue = theme[2] * value;
          trailCursor = this.writeVertex(
            this.trailScratch, trailCursor, beforeIndex,
            red, green, blue, alpha
          );
          trailCursor = this.writeVertex(
            this.trailScratch, trailCursor, afterIndex,
            red, green, blue, alpha
          );
        }

        headCursor = this.writeCoordinates(
          this.headScratch,
          headCursor,
          sampledHead,
          1, 1, 1,
          0.96 * boundaryFade
        );
      }

      return {
        trailFloats: trailCursor,
        trailVertices: trailCursor / FLOATS_PER_VERTEX,
        headFloats: headCursor,
        headVertices: headCursor / FLOATS_PER_VERTEX
      };
    }

    writeVertex(destination, cursor, pointIndex, red, green, blue, alpha) {
      const offset = pointIndex * 3;
      destination[cursor++] = this.points[offset];
      destination[cursor++] = this.points[offset + 1];
      destination[cursor++] = this.points[offset + 2];
      destination[cursor++] = red;
      destination[cursor++] = green;
      destination[cursor++] = blue;
      destination[cursor++] = alpha;
      return cursor;
    }

    writeCoordinates(destination, cursor, coordinates, red, green, blue, alpha) {
      destination[cursor++] = coordinates[0];
      destination[cursor++] = coordinates[1];
      destination[cursor++] = coordinates[2];
      destination[cursor++] = red;
      destination[cursor++] = green;
      destination[cursor++] = blue;
      destination[cursor++] = alpha;
      return cursor;
    }

    boundaryFade(streamPosition) {
      if (this.pointCount <= 1) return 0;
      const width = Math.max(1, Math.min(180, Math.floor((this.pointCount - 1) / 2)));
      const wrappedHead = modulo(streamPosition, this.pointCount);
      const edgeDistance = Math.min(wrappedHead, this.pointCount - 1 - wrappedHead);
      return smootherstep(edgeDistance / width);
    }

    sampleTrajectory(
      position,
      result = new Float32Array(3),
      tangent = new Float32Array(3)
    ) {
      const count = this.pointCount;
      const wrapped = modulo(position, count);
      const index = Math.floor(wrapped);
      const t = wrapped - index;

      for (let axis = 0; axis < 3; axis += 1) {
        const at = (pointIndex) => this.points[pointIndex * 3 + axis];
        if (count >= 4 && index >= 1 && index <= count - 3) {
          const p0 = at(index - 1);
          const p1 = at(index);
          const p2 = at(index + 1);
          const p3 = at(index + 2);
          const t2 = t * t;
          const t3 = t2 * t;
          result[axis] = 0.5 * (
            2 * p1
            + (-p0 + p2) * t
            + (2 * p0 - 5 * p1 + 4 * p2 - p3) * t2
            + (-p0 + 3 * p1 - 3 * p2 + p3) * t3
          );
          tangent[axis] = 0.5 * (
            (-p0 + p2)
            + 2 * (2 * p0 - 5 * p1 + 4 * p2 - p3) * t
            + 3 * (-p0 + 3 * p1 - 3 * p2 + p3) * t2
          );
        } else {
          const nextIndex = Math.min(index + 1, count - 1);
          const start = at(index);
          const delta = index === count - 1
            ? at(count - 1) - at(count - 2)
            : at(nextIndex) - start;
          result[axis] = start + delta * t;
          tangent[axis] = delta;
        }
      }
      return { position: result, tangent };
    }

    themeAt(seconds) {
      const safeSeconds = Math.max(0, Number(seconds) || 0);
      const transition = Math.floor(safeSeconds / THEME_TRANSITION_SECONDS);
      const progress = (safeSeconds % THEME_TRANSITION_SECONDS) / THEME_TRANSITION_SECONDS;
      const amount = smootherstep(progress);
      const start = THEME_COLOURS[transition % THEME_COLOURS.length];
      const end = THEME_COLOURS[(transition + 1) % THEME_COLOURS.length];
      return [
        start[0] + (end[0] - start[0]) * amount,
        start[1] + (end[1] - start[1]) * amount,
        start[2] + (end[2] - start[2]) * amount
      ];
    }

    particleBrightnessAtZoom(zoom, farBrightness, fullBrightnessZoom) {
      const safeFar = clamp(farBrightness, 0, 1);
      const denominator = Math.max(1e-6, fullBrightnessZoom - 2);
      const progress = clamp((zoom - 2) / denominator, 0, 1);
      return safeFar + (1 - safeFar) * smootherstep(progress);
    }

    buildStars() {
      const random = new PythonRandom(20260712);
      const radius = SETTINGS.worldRadius * 2.4;
      const vertices = new Float32Array(SETTINGS.backgroundStars * FLOATS_PER_VERTEX);
      let cursor = 0;
      for (let index = 0; index < SETTINGS.backgroundStars; index += 1) {
        vertices[cursor++] = random.uniform(-radius, radius);
        vertices[cursor++] = random.uniform(-radius, radius);
        vertices[cursor++] = random.uniform(-radius, radius);
        vertices[cursor++] = 0.22;
        vertices[cursor++] = 0.56;
        vertices[cursor++] = 0.94;
        vertices[cursor++] = random.uniform(0.08, 0.28);
      }
      return vertices;
    }

    setCamera(uniforms, aspect, pose, options = {}) {
      const gl = this.gl;
      const pointScale = options.pointScale === undefined ? 1 : options.pointScale;
      const pixelOffset = options.pixelOffset || [0, 0];
      const opacityScale = options.opacityScale === undefined ? 1 : options.opacityScale;
      const glowFalloff = options.glowFalloff === undefined ? 5 : options.glowFalloff;
      const solidCore = options.solidCore ? 1 : 0;

      gl.uniform1f(uniforms.yaw, pose.yaw);
      gl.uniform1f(uniforms.pitch, pose.pitch);
      gl.uniform1f(uniforms.worldRadius, SETTINGS.worldRadius);
      gl.uniform1f(uniforms.aspect, aspect);
      gl.uniform1f(uniforms.zoom, pose.zoom);
      gl.uniform1f(uniforms.pointScale, pointScale);
      gl.uniform1f(uniforms.opacityScale, opacityScale);
      gl.uniform1f(uniforms.farVisibility, SETTINGS.farCurveVisibility);
      if (uniforms.glowFalloff !== null) gl.uniform1f(uniforms.glowFalloff, glowFalloff);
      if (uniforms.solidCore !== null) gl.uniform1f(uniforms.solidCore, solidCore);
      gl.uniform3f(uniforms.target, pose.target[0], pose.target[1], pose.target[2]);
      gl.uniform2f(uniforms.framing, pose.framing[0], pose.framing[1]);
      gl.uniform2f(uniforms.pixelOffset, pixelOffset[0], pixelOffset[1]);
    }

    bindVertexLayout(buffer) {
      const gl = this.gl;
      gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
      gl.enableVertexAttribArray(0);
      gl.vertexAttribPointer(0, 3, gl.FLOAT, false, FLOATS_PER_VERTEX * BYTES_PER_FLOAT, 0);
      gl.enableVertexAttribArray(1);
      gl.vertexAttribPointer(
        1,
        4,
        gl.FLOAT,
        false,
        FLOATS_PER_VERTEX * BYTES_PER_FLOAT,
        3 * BYTES_PER_FLOAT
      );
    }

    uniformsFor(program) {
      const gl = this.gl;
      const location = (name) => gl.getUniformLocation(program, name);
      return {
        yaw: location("uYaw"),
        pitch: location("uPitch"),
        worldRadius: location("uWorldRadius"),
        aspect: location("uAspect"),
        zoom: location("uZoom"),
        pointScale: location("uPointScale"),
        opacityScale: location("uOpacityScale"),
        farVisibility: location("uFarVisibility"),
        glowFalloff: location("uGlowFalloff"),
        solidCore: location("uSolidCore"),
        target: location("uTarget"),
        framing: location("uFraming"),
        pixelOffset: location("uPixelOffset")
      };
    }

    buildProgram(vertexSource, fragmentSource) {
      const gl = this.gl;
      const compile = (type, source) => {
        const shader = gl.createShader(type);
        if (!shader) throw new Error("WebGL could not allocate a shader.");
        gl.shaderSource(shader, source);
        gl.compileShader(shader);
        if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
          const message = gl.getShaderInfoLog(shader) || "unknown shader compile error";
          gl.deleteShader(shader);
          throw new Error(message);
        }
        return shader;
      };

      const vertexShader = compile(gl.VERTEX_SHADER, vertexSource);
      const fragmentShader = compile(gl.FRAGMENT_SHADER, fragmentSource);
      const program = gl.createProgram();
      if (!program) throw new Error("WebGL could not allocate a shader program.");
      gl.attachShader(program, vertexShader);
      gl.attachShader(program, fragmentShader);
      gl.bindAttribLocation(program, 0, "aPosition");
      gl.bindAttribLocation(program, 1, "aColour");
      gl.linkProgram(program);
      gl.deleteShader(vertexShader);
      gl.deleteShader(fragmentShader);
      if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
        const message = gl.getProgramInfoLog(program) || "unknown shader link error";
        gl.deleteProgram(program);
        throw new Error(message);
      }
      return program;
    }
  }

  Object.defineProperty(window, "ChaosExactRenderer", {
    value: ChaosExactRenderer,
    configurable: true,
    writable: false
  });
})();
