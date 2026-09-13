/* Stable random directions; grouped objects turn about their own centres. */
(function(host){
  'use strict';
  function entrancePositions(grains,width,height){
    const aspect=width/height,fit=Math.min(.68,aspect*.84),t=Math.max(0,Math.min(1,(aspect-.8)/.5)),centre=.05+.15*t*t*(3-2*t);
    const points=new Float32Array(grains.length/4*3);
    for(let i=0;i<points.length/3;i++){
      const g=i*4,a=((grains[g+1]*13.17+grains[g+3]*7.29)%1)*Math.PI*2,c=Math.cos(a),s=Math.sin(a);
      const margin=1.08+.55*((grains[g]*17.31+grains[g+2]*31.73)%1),radius=margin/Math.max(Math.abs(c),Math.abs(s));
      // Place every grain beyond a viewport edge. Neutral-camera projection
      // is exact in both portrait and landscape, including fullscreen resize.
      points[i*3]=c*radius*aspect/fit;points[i*3+1]=(s*radius-centre)/fit;points[i*3+2]=0;
    }
    return points;
  }
  function create(random=Math.random){
    const directions=Array.from({length:10},()=>random()<.5?-1:1);
    const axis=()=>{const z=2*random()-1,a=2*Math.PI*random(),r=Math.sqrt(1-z*z);return [r*Math.cos(a),r*Math.sin(a),z];};
    const axes={6:Array.from({length:5},axis),7:Array.from({length:2},axis)};
    function sceneDirection(state){
      if(!state.moving)return directions[state.scene];
      const p=Math.max(0,Math.min(1,state.progress)),e=p*p*p*(p*(p*6-15)+10);
      return directions[state.from]+(directions[state.to]-directions[state.from])*e;
    }
    function objectSteps(scene,angle){return (axes[scene]||[]).map((axis,index)=>({index,axis:[...axis],angle:angle*(scene===6?2:1)}));}
    return Object.freeze({sceneDirection,objectSteps,evidence:()=>({directions:[...directions],axes:JSON.parse(JSON.stringify(axes)),polyhedronSpeedMultiplier:2})});
  }
  host.CourseOpeningMotion=Object.freeze({create,entrancePositions});
})(typeof window!=='undefined'?window:globalThis);
