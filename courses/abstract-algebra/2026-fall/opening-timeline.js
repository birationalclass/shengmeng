/* Canonical, reversible time for the particle opening. No animation frames or DOM state. */
(function (host) {
  'use strict';

  function finite(value, name) {
    if (typeof value !== 'number' || !Number.isFinite(value)) {
      throw new TypeError(name + ' must be a finite number.');
    }
    return value;
  }

  function create(options) {
    const holds = options && options.holds;
    const transitions = options && options.transitions;
    if (!Array.isArray(holds) || !holds.length || !Array.isArray(transitions) || transitions.length !== holds.length) {
      throw new TypeError('Provide equally sized, nonempty holds and transitions arrays.');
    }
    const holdTimes = holds.map((value) => {
      finite(value, 'Hold duration');
      if (value < 0) throw new RangeError('Hold durations cannot be negative.');
      return value;
    });
    const transitionTimes = transitions.map((value) => {
      finite(value, 'Transition duration');
      if (value <= 0) throw new RangeError('Transition durations must be positive.');
      return value;
    });
    const segments = [];
    const starts = [];
    let duration = 0;
    for (let i = 0; i < holdTimes.length; i++) {
      starts.push(duration);
      if (holdTimes[i] > 0) {
        segments.push({ start: duration, end: duration + holdTimes[i], from: i, to: i, moving: false });
        duration += holdTimes[i];
      }
      segments.push({ start: duration, end: duration + transitionTimes[i], from: i, to: (i + 1) % holdTimes.length, moving: true });
      duration += transitionTimes[i];
    }
    finite(duration, 'Total duration');

    let position = 0;
    let cycles = 0;
    let direction = 1;

    function segmentAtPosition() {
      // Half-open intervals make every boundary unambiguous. Both adjacent
      // intervals have identical geometry at that instant, including the seam.
      let lo = 0;
      let hi = segments.length - 1;
      while (lo < hi) {
        const mid = (lo + hi) >> 1;
        if (position < segments[mid].end) hi = mid;
        else lo = mid + 1;
      }
      return segments[lo];
    }

    function state() {
      const segment = segmentAtPosition();
      const elapsed = position - segment.start;
      return {
        from: segment.from,
        to: segment.to,
        progress: segment.moving ? elapsed / (segment.end - segment.start) : 1,
        moving: segment.moving,
        scene: segment.to,
        holdElapsed: segment.moving ? 0 : elapsed,
        holdDuration: holdTimes[segment.to],
        direction,
        position,
        cycles
      };
    }

    function normalize(value) {
      let wrapped = value % duration;
      if (wrapped < 0) wrapped += duration;
      // Extremely small negative values can round up to duration. Mapping that
      // representation to zero avoids an impossible out-of-range segment.
      if (wrapped >= duration) wrapped = 0;
      return wrapped === 0 ? 0 : wrapped;
    }

    function advance(deltaMs) {
      finite(deltaMs, 'Elapsed time');
      const next = position + deltaMs * direction;
      finite(next, 'Resulting time');
      cycles += Math.floor(next / duration);
      position = normalize(next);
      return state();
    }

    function seek(time) {
      finite(time, 'Seek time');
      cycles = Math.floor(time / duration);
      position = normalize(time);
      return state();
    }

    function setDirection(value, engage = false) {
      if (value !== 1 && value !== -1) throw new RangeError('Direction must be +1 or -1.');
      direction = value;
      const segment = segmentAtPosition();
      if (engage && !segment.moving) {
        // Skip only stationary time. We never exchange morph endpoints or
        // change progress during a morph, so reversing retraces the same path.
        position = direction > 0 ? segment.end : starts[segment.from];
      }
      return state();
    }

    return Object.freeze({ state, advance, setDirection, seek, duration });
  }

  host.CourseOpeningTimeline = Object.freeze({ create });
})(typeof window !== 'undefined' ? window : globalThis);
