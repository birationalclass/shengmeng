(() => {
  "use strict";

  const MODE_FREE = "FREE";
  const MODE_CINEMATIC = "CINEMATIC";
  const MODE_MANUAL = "MANUAL";
  const MODES = Object.freeze([MODE_FREE, MODE_CINEMATIC, MODE_MANUAL]);
  const SHOT_CYCLE_SECONDS = 90;
  const CINEMATIC_DURATION_SECONDS = 183;
  const MANUAL_RESPONSE_PER_SECOND = 18;

  const CINEMATIC_KEYFRAMES = Object.freeze([
    [0,   pose(-0.70, 0.20, 0.90)],
    [18,  pose(-0.36, 0.46, 1.02)],
    [42,  pose(0.14, 1.05, 1.28, [0, 0, 0], [0, 0.12])],
    [66,  pose(0.62, 0.88, 1.10)],
    [94,  pose(1.30, 0.96, 1.34, [0, 0, 0], [0, 0.10])],
    [117, pose(1.92, 0.50, 1.62, [0, 0, 0], [-0.03, 0.02])],
    [135, pose(2.52, 0.13, 2.72, [0, 0, 0], [-0.05, -0.02])],
    [150, pose(3.16, 0.36, 1.72, [0, 0, 0], [0.02, 0.02])],
    [169, pose(4.02, 0.86, 1.32, [3.5, 0, 0], [0.13, 0.28])],
    [183, pose(4.70, 0.38, 1.05, [2, 0, 0], [0.06, 0.05])]
  ]);

  function pose(yaw, pitch, zoom, target = [0, 0, 0], framing = [0, 0]) {
    return { yaw, pitch, zoom, target: target.slice(), framing: framing.slice() };
  }

  function clamp(value, minimum, maximum) {
    return Math.max(minimum, Math.min(maximum, value));
  }

  function blend(first, second, amount) {
    return first + (second - first) * amount;
  }

  function smoothstep(value) {
    const clamped = clamp(value, 0, 1);
    return clamped * clamped * (3 - 2 * clamped);
  }

  function smootherstep(value) {
    const clamped = clamp(value, 0, 1);
    return clamped ** 3 * (clamped * (clamped * 6 - 15) + 10);
  }

  function positiveModulo(value, modulus) {
    return ((value % modulus) + modulus) % modulus;
  }

  // Python's round() resolves exact half-integers to the nearest even integer.
  function roundTiesToEven(value) {
    const lower = Math.floor(value);
    const fraction = value - lower;
    if (fraction < 0.5) return lower;
    if (fraction > 0.5) return lower + 1;
    return lower % 2 === 0 ? lower : lower + 1;
  }

  function interpolatePose(start, end, amount) {
    return pose(
      blend(start.yaw, end.yaw, amount),
      blend(start.pitch, end.pitch, amount),
      blend(start.zoom, end.zoom, amount),
      start.target.map((value, index) => blend(value, end.target[index], amount)),
      start.framing.map((value, index) => blend(value, end.framing[index], amount))
    );
  }

  function cinematicPoseAt(seconds) {
    const localSeconds = positiveModulo(seconds, CINEMATIC_DURATION_SECONDS);
    for (let index = 0; index < CINEMATIC_KEYFRAMES.length - 1; index += 1) {
      const [startSeconds, startPose] = CINEMATIC_KEYFRAMES[index];
      const [endSeconds, endPose] = CINEMATIC_KEYFRAMES[index + 1];
      if (localSeconds <= endSeconds) {
        const progress = (localSeconds - startSeconds) / (endSeconds - startSeconds);
        return interpolatePose(startPose, endPose, smoothstep(progress));
      }
    }
    const finalPose = CINEMATIC_KEYFRAMES[CINEMATIC_KEYFRAMES.length - 1][1];
    return pose(finalPose.yaw, finalPose.pitch, finalPose.zoom, finalPose.target, finalPose.framing);
  }

  function followWeightAt(seconds) {
    const local = positiveModulo(Math.max(0, seconds), SHOT_CYCLE_SECONDS);
    if (local < 8) return 0;
    if (local < 32) return smootherstep((local - 8) / 24);
    if (local < 64) return 1;
    if (local < 88) return 1 - smootherstep((local - 64) / 24);
    return 0;
  }

  function macroYawAt(seconds) {
    return 0.020 * seconds + 0.12 * Math.sin(seconds / 32);
  }

  function freePoseAt(seconds, followTarget, followYaw) {
    const followWeight = followWeightAt(seconds);
    const macroYaw = macroYawAt(seconds);
    const macroPitch = (
      0.54
      + 0.20 * Math.sin(seconds / 36)
      + 0.04 * Math.sin(seconds / 16)
    );
    const macroZoom = 2 * (
      1.02
      + 0.08 * Math.sin(seconds / 30)
      + 0.03 * Math.sin(seconds / 14 + 0.7)
    );

    return pose(
      blend(macroYaw, followYaw, followWeight),
      blend(macroPitch, 0.05, followWeight),
      blend(macroZoom, 30, followWeight),
      [0, 0, 0].map((value, index) => blend(value, followTarget[index], followWeight)),
      [0, 0]
    );
  }

  class ChaosCameraRig {
    static MODE_FREE = MODE_FREE;
    static MODE_CINEMATIC = MODE_CINEMATIC;
    static MODE_MANUAL = MODE_MANUAL;
    static MODES = MODES;
    static SHOT_CYCLE_SECONDS = SHOT_CYCLE_SECONDS;
    static CINEMATIC_DURATION_SECONDS = CINEMATIC_DURATION_SECONDS;
    static MANUAL_RESPONSE_PER_SECOND = MANUAL_RESPONSE_PER_SECOND;
    static WORLD_RADIUS = 30;
    static DISPLAY_RADIUS = 17.4;

    constructor() {
      this.reset();
    }

    get mode() {
      return this._mode;
    }

    poseAt(seconds) {
      let base;
      if (this._mode === MODE_FREE) {
        base = freePoseAt(seconds, this._trackedTarget, this._trackedFollowYaw);
      } else if (this._mode === MODE_CINEMATIC) {
        base = cinematicPoseAt(seconds);
      } else {
        base = pose(0, 0.42, 1);
      }

      return pose(
        base.yaw + this.yawOffset,
        clamp(base.pitch + this.pitchOffset, -1.25, 1.25),
        clamp(base.zoom * this.zoomMultiplier, 0.18, 36),
        base.target.map((value, index) => value + this.targetOffset[index]),
        base.framing
      );
    }

    followStreamAt(seconds, streamCount) {
      if (streamCount <= 0) {
        throw new RangeError("streamCount must be positive");
      }
      const cycle = Math.floor(Math.max(0, seconds) / SHOT_CYCLE_SECONDS);
      return (11 + cycle * 37) % streamCount;
    }

    updateFollowTarget(target, direction, elapsedSeconds, seconds) {
      if (!this._hasTrackingTarget) {
        this._trackedTarget = target.slice();
        this._trackedVelocity = [0, 0, 0];
        this._hasTrackingTarget = true;
      } else {
        const deltaTime = Math.max(0, elapsedSeconds);
        let desiredVelocity = target.map((desired, index) => (
          (desired - this._trackedTarget[index]) * 0.65
        ));
        const desiredSpeed = Math.hypot(...desiredVelocity);
        if (desiredSpeed > 2) {
          desiredVelocity = desiredVelocity.map((value) => value * 2 / desiredSpeed);
        }
        const velocityBlend = 1 - Math.exp(-2 * deltaTime);
        this._trackedVelocity = this._trackedVelocity.map((current, index) => (
          current + (desiredVelocity[index] - current) * velocityBlend
        ));
        this._trackedTarget = this._trackedTarget.map((current, index) => (
          current + this._trackedVelocity[index] * deltaTime
        ));
      }

      const dx = direction[0];
      const dz = direction[2];
      const cycle = Math.floor(Math.max(0, seconds) / SHOT_CYCLE_SECONDS);
      if (cycle !== this._followYawCycle && Math.abs(dx) + Math.abs(dz) > 1e-9) {
        const desiredYaw = Math.atan2(dz, dx);
        const referenceSeconds = cycle * SHOT_CYCLE_SECONDS + 20;
        const referenceYaw = macroYawAt(referenceSeconds);
        const turns = roundTiesToEven((referenceYaw - desiredYaw) / (2 * Math.PI));
        this._trackedFollowYaw = desiredYaw + turns * 2 * Math.PI;
        this._followYawCycle = cycle;
      }
    }

    orbit(deltaX, deltaY) {
      this._desiredYawOffset += deltaX * 0.006;
      this._desiredPitchOffset = clamp(
        this._desiredPitchOffset + deltaY * 0.004,
        -0.88,
        0.88
      );
    }

    pan(deltaX, deltaY) {
      this._desiredTargetOffset = [
        this._desiredTargetOffset[0] - deltaX * 0.035,
        this._desiredTargetOffset[1] + deltaY * 0.035,
        this._desiredTargetOffset[2]
      ];
    }

    dolly(wheelDelta) {
      this._desiredZoomMultiplier = clamp(
        this._desiredZoomMultiplier * (1.10 ** wheelDelta),
        0.18,
        10
      );
    }

    advanceManualMotion(elapsedSeconds) {
      const deltaTime = Math.max(0, elapsedSeconds);
      const amount = 1 - Math.exp(-MANUAL_RESPONSE_PER_SECOND * deltaTime);
      this.yawOffset += (this._desiredYawOffset - this.yawOffset) * amount;
      this.pitchOffset += (this._desiredPitchOffset - this.pitchOffset) * amount;
      this.zoomMultiplier += (
        this._desiredZoomMultiplier - this.zoomMultiplier
      ) * amount;
      this.targetOffset = this.targetOffset.map((current, index) => (
        current + (this._desiredTargetOffset[index] - current) * amount
      ));
    }

    cycleMode() {
      const index = (MODES.indexOf(this._mode) + 1) % MODES.length;
      this._mode = MODES[index];
      return this._mode;
    }

    reset() {
      this._mode = MODE_FREE;
      this.yawOffset = 0;
      this.pitchOffset = 0;
      this.zoomMultiplier = 1;
      this.targetOffset = [0, 0, 0];
      this._desiredYawOffset = 0;
      this._desiredPitchOffset = 0;
      this._desiredZoomMultiplier = 1;
      this._desiredTargetOffset = [0, 0, 0];
      this._trackedTarget = [0, 0, 0];
      this._trackedVelocity = [0, 0, 0];
      this._hasTrackingTarget = false;
      this._trackedFollowYaw = 0;
      this._followYawCycle = -1;
    }
  }

  const globalScope = typeof window === "undefined" ? globalThis : window;
  globalScope.ChaosCameraRig = ChaosCameraRig;
})();
