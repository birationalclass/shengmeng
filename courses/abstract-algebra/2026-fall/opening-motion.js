/* Stable random directions; grouped objects turn about their own centres. */
(function(host){
  'use strict';
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
  host.CourseOpeningMotion=Object.freeze({create});
})(typeof window!=='undefined'?window:globalThis);
