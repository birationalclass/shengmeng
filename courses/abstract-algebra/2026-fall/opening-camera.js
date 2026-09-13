/* One continuous, reversible macro shot per mathematical figure.
 * There are no independently eased keyframe segments: the camera follows a
 * single smooth path from the complete figure to an actual surface point,
 * passes around that point at 10x scale, and returns to its opening framing.
 */
(() => {
  'use strict';
  const clamp = value => Math.max(0, Math.min(1, Number.isFinite(value) ? value : 0));
  const ease = value => {const t=clamp(value);return t*t*t*(t*(t*6-15)+10);};
  const neutral = Object.freeze({angles:Object.freeze([-.08,0,0]),zoom:1,target:Object.freeze([0,0,0])});
  // pitch, pitch travel, yaw centre, yaw travel, roll. A slow continuous arc
  // remains visible during the close pass; it never pauses at intermediate keys.
  const shots = Object.freeze([
    Object.freeze([-.31, .035,-.06, .11, .008]),
    Object.freeze([-.35,-.030, .07,-.12,-.008]),
    Object.freeze([-.29, .040, .03, .14, .007]),
    Object.freeze([-.23, .030,-.04,-.11,-.004]),
    Object.freeze([-.28,-.040, .08, .11, .012]),
    Object.freeze([-.16, .025, .10,-.12, .008])
  ]);
  const focuses = shots.map(()=>[0,0,0]);
  // Integrate a quintic velocity ramp rather than repeatedly easing poses.
  // At the default ten-second duration, each five-second leg accelerates for
  // 1.5 seconds, cruises for two seconds, and decelerates for 1.5 seconds.
  // Position, velocity, acceleration and jerk join continuously. The reversal
  // at the close view is equally smooth and does not impose a frozen hold.
  const accelerationFraction=.30;
  const integratedEase=t=>t*t*t*t*(t*t-3*t+2.5);
  function distanceAt(value) {
    const u=clamp(value),r=accelerationFraction;
    if(u<r)return r*integratedEase(u/r)/(1-r);
    if(u>1-r)return 1-r*integratedEase((1-u)/r)/(1-r);
    return (u-r/2)/(1-r);
  }
  function point(value) {
    return value&&value.length>=3&&[value[0],value[1],value[2]].every(Number.isFinite)
      ? [value[0],value[1],value[2]] : [0,0,0];
  }
  function indexOf(scene) {
    const number=Number(scene),integer=Number.isFinite(number)?Math.floor(number):0;
    return ((integer%shots.length)+shots.length)%shots.length;
  }
  function setFocuses(values) {
    if(!values||values.length!==shots.length)throw new RangeError('One surface focus is required for each opening figure');
    for(let scene=0;scene<shots.length;scene++)focuses[scene]=point(values[scene]);
  }
  function blend(first,second,amount) {
    const t=clamp(Number(amount));
    const start=point(first.target),finish=point(second.target);
    return {
      angles:first.angles.map((angle,index)=>angle+(second.angles[index]-angle)*t),
      zoom:Math.max(1,first.zoom+(second.zoom-first.zoom)*t),
      target:start.map((coordinate,index)=>coordinate+(finish[index]-coordinate)*t)
    };
  }
  function sample(scene,phase,focus) {
    const index=indexOf(scene),shot=shots[index],t=clamp(Number(phase));
    // Return the exact same endpoint poses, including at the loop seam.
    if(t===0||t===1)return {angles:[...neutral.angles],zoom:1,target:[0,0,0]};
    const s=ease(t),arc=distanceAt(2*Math.min(t,1-t)),travel=2*s-1;
    // A logarithmic dolly with a bounded cruising speed. In a ten-second shot
    // the largest zoom ratio per 60 Hz frame is about 1.011, under half the
    // peak rate of the earlier concentrated push. Longer selected durations
    // slow this same complete shot proportionally; 10 seconds still means
    // ten seconds for both the approach and return together.
    const zoom=Math.exp(Math.LN10*arc);
    // In orthographic screen coordinates, the selected point's distance from
    // the viewing centre becomes focus * (1-arc)^2. It approaches monotonically
    // despite the 10x magnification, avoiding sideways acceleration or empty
    // centre-hole closeups. The target is exactly on the surface at full zoom.
    const focusWeight=1-(1-arc)*(1-arc)/zoom,at=focus===undefined?focuses[index]:point(focus);
    return {
      angles:[neutral.angles[0]+arc*(shot[0]+shot[1]*travel),arc*(shot[2]+shot[3]*travel),arc*shot[4]],
      zoom:Math.max(1,Math.min(10,zoom)),
      target:at.map(coordinate=>coordinate*focusWeight)
    };
  }
  window.CourseOpeningCamera=Object.freeze({
    count:shots.length,sample,blend,setFocuses,neutral,
    // Manual orbit retains the homepage PDE camera's calibrated sensitivity.
    manual:Object.freeze({yawPerPixel:.006,pitchPerPixel:.004,responsePerSecond:18,pitchLimit:.88}),
    evidence:()=>({
      source:'Original continuous macro shot; manual orbit calibration from visuals/chaos/exact-camera.js',
      approach:'Continuous slow orbit; integrated C3 velocity ramps; logarithmic 1x-10x-1x dolly; projection-synchronised surface focus',
      scenes:shots.length,zoomRange:[1,10],macroPhase:[.425,.575],
      accelerationFractionPerLeg:accelerationFraction,maxLogZoomRateAtTenSeconds:Math.LN10/(5*(1-accelerationFraction)),
      endpointPose:{angles:[...neutral.angles],zoom:1,target:[0,0,0]},
      focuses:focuses.map(focus=>[...focus])
    })
  });
})();
