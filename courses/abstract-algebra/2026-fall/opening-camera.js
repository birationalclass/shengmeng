/* Per-figure camera choreography adapted from this site's PDE film camera:
 * visuals/chaos/exact-camera.js, CINEMATIC_KEYFRAMES / interpolatePose.
 * Its yaw + pitch orbit and push-in / pull-back are retained at a smaller scale;
 * shots stay within the full sculpture's framing instead of entering the PDE.
 * Sampling depends only on scene and phase, so reversed time retraces the camera.
 */
(() => {
  'use strict';
  const clamp = value => Math.max(0, Math.min(1, Number.isFinite(value) ? value : 0));
  // The PDE camera also uses smootherstep for its approach and departure.
  // Here C2 easing gives each very short shot a quiet start and finish.
  const ease = value => {const t=clamp(value);return t*t*t*(t*(t*6-15)+10);};
  const key = (phase,pitch,yaw,roll,zoom) => Object.freeze({phase,angles:Object.freeze([pitch,yaw,roll]),zoom});
  const shots = Object.freeze([
    // Rose: reveal the thickness, approach the petals, recover the whole motif.
    Object.freeze([
      key(0,   -.10,-.48,-.025,.95),
      key(.24, -.38,-.22, .010,1.01),
      key(.51, -.68, .17, .025,1.10),
      key(.77, -.30, .44, .014,1.045),
      key(1,    .10, .26,-.012,.98)
    ]),
    // Star: counter-orbit, with its strongest relief at the nearest viewpoint.
    Object.freeze([
      key(0,   -.12, .44, .015,.97),
      key(.24, -.42, .24,-.010,1.055),
      key(.53, -.64,-.16,-.028,1.11),
      key(.78, -.22,-.48,-.010,1.035),
      key(1,    .12,-.28, .008,.98)
    ]),
    // Window: a low oblique pass opens back into the twelvefold composition.
    Object.freeze([
      key(0,   -.12,-.42,-.025,.94),
      key(.27, -.48,-.10, .000,1.04),
      key(.56, -.69, .26, .024,1.095),
      key(.81, -.24, .47, .012,1.035),
      key(1,    .12, .24,-.010,.98)
    ]),
    // E8: shallower approach preserves the legibility of its eight root rings.
    Object.freeze([
      key(0,    .10,-.40,-.012,.95),
      key(.25, -.26,-.25, .005,1.015),
      key(.53, -.56, .15, .022,1.075),
      key(.79, -.24, .46, .010,1.025),
      key(1,    .15, .40,-.008,.98)
    ]),
    // Julia: follow its diagonal branches while revealing their raised grains.
    Object.freeze([
      key(0,   -.08, .40, .020,.97),
      key(.27, -.42, .20,-.005,1.07),
      key(.55, -.60,-.20,-.025,1.11),
      key(.80, -.23,-.46,-.012,1.025),
      key(1,    .12,-.42, .010,.98)
    ]),
    // Ring: the geometry already has a 55-degree tilt. This pass moves from
    // its lip to its open interior; a smaller dolly leaves room for its depth.
    Object.freeze([
      key(0,   -.12,-.45,-.020,.97),
      key(.24,  .24,-.20,-.010,1.055),
      key(.50, -.20, .10, .015,1.08),
      key(.78, -.66, .35, .022,1.00),
      key(1,   -.35, .50, .005,.94)
    ])
  ]);
  function blend(first,second,amount) {
    const t=clamp(amount);
    return {
      angles:first.angles.map((angle,index)=>angle+(second.angles[index]-angle)*t),
      zoom:first.zoom+(second.zoom-first.zoom)*t
    };
  }
  function sample(scene,phase) {
    const numeric=Number.isFinite(Number(scene))?Math.floor(Number(scene)):0;
    const keys=shots[((numeric%shots.length)+shots.length)%shots.length];
    const t=clamp(Number(phase));
    for(let index=0;index<keys.length-1;index++) {
      if(t<=keys[index+1].phase) {
        const first=keys[index],second=keys[index+1];
        return blend(first,second,ease((t-first.phase)/(second.phase-first.phase)));
      }
    }
    return blend(keys[keys.length-1],keys[keys.length-1],0);
  }
  window.CourseOpeningCamera=Object.freeze({
    count:shots.length,
    sample,
    blend,
    // These are the homepage PDE camera's own orbit sensitivity and damping.
    manual:Object.freeze({yawPerPixel:.006,pitchPerPixel:.004,responsePerSecond:18,pitchLimit:.88}),
    evidence:()=>({
      source:'visuals/chaos/exact-camera.js',
      approach:'CINEMATIC_KEYFRAMES + yaw/pitch orbit + dolly + smootherstep',
      scenes:shots.length,
      keyframesPerScene:shots.map(keys=>keys.length),
      pitchRange:[-.69,.24],yawRange:[-.48,.50],zoomRange:[.94,1.11]
    })
  });
})();
