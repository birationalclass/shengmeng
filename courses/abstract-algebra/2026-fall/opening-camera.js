/* One spatial camera route for the whole selected-figure cycle.
 * Orbit, framing and magnification share canonical time. Figure changes never
 * reset the camera or start another identical push-pull shot. The analytical
 * closed orbit and C3 detail envelope are reversible and join at the loop seam.
 */
(() => {
  'use strict';
  const TAU = 2 * Math.PI, COUNT = 10;
  const clamp = value => Math.max(0, Math.min(1, Number.isFinite(value) ? value : 0));
  const ease = value => {const t=clamp(value);return t*t*t*(t*(t*6-15)+10);};
  const neutral = Object.freeze({angles:Object.freeze([-.14,0,0]),zoom:1,target:Object.freeze([0,0,0])});
  const focuses = Array.from({length:COUNT},()=>[0,0,0]);
  // The old portrait return occupied 45% of a transition. A full transition
  // scaled by 1.35 therefore gives precisely three times that return duration.
  const portraitTransitionScale=1.35;
  const defaultTransitions = [8400,8400,8400,10400,10800,10000,10000,10000,10000,10000]
    .map((duration,scene)=>scene===8||scene===9?duration*portraitTransitionScale:duration);
  // A figure's selected interval is its viewing time. Formation belongs to
  // the following transition and no longer consumes that viewing time.
  const defaultHolds = Array(COUNT).fill(30000);
  let defaultDuration=0;
  const defaultStarts = defaultHolds.map((hold,i)=>{const start=defaultDuration;defaultDuration+=hold+defaultTransitions[i];return start;});
  const defaultRoute = {holds:defaultHolds,transitions:defaultTransitions,starts:defaultStarts,duration:defaultDuration};
  const detailScene = 3, accelerationFraction = .20;
  const integratedEase = t => t*t*t*t*(t*t-3*t+2.5);

  // Integral of a quintic acceleration ramp. Unlike easing several camera
  // keys, this controls velocity itself: a gentle launch, a quiet cruise and
  // a smooth arrival, with continuous position through third derivative.
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
    const integer=Number.isFinite(Number(scene))?Math.floor(Number(scene)):0;
    return ((integer%COUNT)+COUNT)%COUNT;
  }
  function setFocuses(values) {
    if(!values||values.length!==COUNT)throw new RangeError('One surface focus is required for each opening figure');
    for(let scene=0;scene<COUNT;scene++)focuses[scene]=point(values[scene]);
  }
  function blend(first,second,amount) {
    const t=clamp(Number(amount)),start=point(first.target),finish=point(second.target);
    return {
      angles:first.angles.map((angle,index)=>angle+(second.angles[index]-angle)*t),
      zoom:Math.max(1,first.zoom+(second.zoom-first.zoom)*t),
      target:start.map((coordinate,index)=>coordinate+(finish[index]-coordinate)*t)
    };
  }
  function orbitAt(u) {
    // A cycloidal phase has zero velocity and acceleration at the initial
    // wide view. Its periodic first and second harmonics describe a gently
    // banking spatial oval; no individual image owns or restarts that oval.
    const angle=TAU*u-Math.sin(TAU*u);
    return [
      -.14 + .18*(Math.sin(angle+.9)-Math.sin(.9)) - .08*Math.sin(2*angle),
      .38*Math.sin(angle)+.10*Math.sin(2*angle),
      .025*(Math.sin(angle-.4)+Math.sin(.4))
    ];
  }
  function baseLogZoom(u) {
    // The broad camera drift spans three figures in each direction. During
    // some figures it pushes, during others it continues an orbit at almost
    // fixed magnification; it never pulls farther back than the first frame.
    return Math.log(2.35)*.5*(1-Math.cos(TAU*u));
  }
  function sampleTimeline(state,route=defaultRoute) {
    const duration=Number(route.duration)>0?Number(route.duration):defaultRoute.duration;
    const position=((Number(state.position)||0)%duration+duration)%duration;
    const phaseOffset=Number.isFinite(route.phaseOffset)?route.phaseOffset:0;
    const u=((position/duration+phaseOffset)%1+1)%1;
    const holds=route.holds||defaultHolds,starts=route.starts||defaultStarts;
    let logarithm=baseLogZoom(u);
    const detailSlot=route.sceneIds?route.sceneIds.indexOf(detailScene):detailScene;
    const macroStart=starts[detailSlot],macroDuration=holds[detailSlot];
    if(macroDuration>0&&position>macroStart&&position<macroStart+macroDuration) {
      const phase=(position-macroStart)/macroDuration;
      const envelope=distanceAt(2*Math.min(phase,1-phase));
      // Only this detail pass reaches 10x. At default 30-second viewing times its
      // log-zoom speed stays below .20 per second (previously .66). If an
      // interval is shortened, reduce the detail depth instead of racing.
      const startPhase=macroStart/duration+phaseOffset,endPhase=startPhase+macroDuration/duration;
      const centreBase=baseLogZoom((startPhase+endPhase)/2),endBase=baseLogZoom(endPhase);
      const intervalBasePeak=Math.floor(startPhase-.5)!==Math.floor(endPhase-.5)
        ?Math.log(2.35):Math.max(baseLogZoom(startPhase),endBase);
      const safePeak=Math.max(intervalBasePeak,Math.min(Math.LN10,centreBase+.205*(macroDuration/2000)*(1-accelerationFraction)));
      logarithm+=(safePeak-logarithm)*envelope;
    }
    const zoom=Math.exp(logarithm);
    const from=indexOf(state.from===undefined?state.scene:state.from);
    const to=indexOf(state.to===undefined?state.scene:state.to);
    const interpolation=state.moving?ease(Number(state.progress)):0;
    const focus=focuses[from].map((coordinate,axis)=>coordinate+(focuses[to][axis]-coordinate)*interpolation);
    // Keep the chosen real surface point nearly fixed in the image while
    // dollying. Its projected displacement scales as zoom^(-1/4), rather
    // than zoom itself, so a close pass does not fling the motif sideways.
    const focusWeight=1-Math.pow(zoom,-1.25);
    return {angles:orbitAt(u),zoom:Math.max(1,zoom),target:focus.map(coordinate=>coordinate*focusWeight)};
  }
  // The portrait returns throughout its extended formation instead of snapping
  // upright in its first 45%. Canonical time makes reverse playback identical.
  function portraitWeight(state){
    if(!state.moving)return state.scene===9?1:0;
    if(state.from===9&&state.to===9)return 1;
    if(state.to===9)return ease(state.progress);
    if(state.from===9)return ease(1-state.progress);
    return 0;
  }
  const groupReturnMs=3000;
  // Restore grouped layouts within three seconds of entering their
  // morph, including reverse playback. Keep that framing throughout the hold.
  function groupWeight(state,transitionDuration=10000){
    const grouped=id=>id===6||id===7;
    if(!state.moving)return grouped(state.scene)?1:0;
    if(grouped(state.from)&&grouped(state.to))return 1;
    const duration=Math.max(1,Number(transitionDuration)||10000);
    const fraction=Math.min(1,groupReturnMs/duration);
    if(grouped(state.to))return clamp(ease(state.progress/fraction));
    if(grouped(state.from))return clamp(ease((1-state.progress)/fraction));
    return 0;
  }
  function frameGroup(view,weight){
    return {...view,...blend(view,{angles:view.angles,zoom:1,target:[0,0,0]},weight)};
  }
  function sample(scene,phase,focus) {
    const index=indexOf(scene),holdElapsed=clamp(Number(phase))*defaultHolds[index];
    const state={from:index,to:index,scene:index,position:defaultStarts[index]+holdElapsed,moving:false};
    const pose=sampleTimeline(state,defaultRoute);
    if(focus!==undefined)pose.target=point(focus).map(coordinate=>coordinate*(1-Math.pow(pose.zoom,-1.25)));
    return pose;
  }
  window.CourseOpeningCamera=Object.freeze({
    count:COUNT,sample,sampleTimeline,blend,setFocuses,neutral,portraitWeight,portraitTransitionScale,groupWeight,frameGroup,groupReturnMs,
    manual:Object.freeze({yawPerPixel:.006,pitchPerPixel:.004,responsePerSecond:18,pitchLimit:.88}),
    evidence:()=>({
      source:'Original continuous whole-cycle spatial route; manual calibration from visuals/chaos/exact-camera.js',
      approach:'Periodic spatial oval; cycloidal launch; independent slow broad dolly; one velocity-ramped E8 macro pass; surface-locked framing',
      scenes:COUNT,zoomRange:[1,10],defaultSwitchInterval:30,defaultHoldSeconds:30,defaultCycleSeconds:defaultDuration/1000,
      detailScene,accelerationFractionPerLeg:accelerationFraction,
      phaseOffset:'Normalized whole-loop offset; add old position/duration minus new position/duration when editing timing',
      endpointPose:{angles:[...neutral.angles],zoom:1,target:[0,0,0]},
      focuses:focuses.map(focus=>[...focus])
    })
  });
})();
