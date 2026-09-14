/* A two-line sand inscription, sampled once before the opening becomes ready. */
(() => {
  'use strict';
  window.CourseOpeningOutro={create(count){
    const lettering=window.CourseOpeningLetteringData;
    if(!lettering)throw new Error('The fixed closing inscription has not loaded');
    const ink=lettering.pixels('outro');
    let seed=137;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
    const points=[];
    for(let i=0;i<count;i++){
      const pixel=ink[Math.floor(random()*ink.length)],x=((pixel%1600)+random()-800)/640,y=(400-Math.floor(pixel/1600)-random())/640;
      // Row 470 lies in the empty gap between Algebra I and the signature.
      points.push([x,y,(random()-.5)*.004,Math.floor(pixel/1600)>470?1:0]);
    }
    // An angular ordering follows the same broad correspondence as the figures.
    points.sort((a,b)=>Math.atan2(a[1],a[0])-Math.atan2(b[1],b[0])||Math.hypot(a[0],a[1])-Math.hypot(b[0],b[1]));
    const positions=new Float32Array(count*3),normals=new Float32Array(count*3),signatureWeights=new Float32Array(count);
    points.forEach((point,i)=>{positions[i*3]=point[0];positions[i*3+1]=point[1];positions[i*3+2]=point[2];normals[i*3+2]=1;signatureWeights[i]=point[3];});
    return{positions,normals,signatureWeights};
  }};
})();
