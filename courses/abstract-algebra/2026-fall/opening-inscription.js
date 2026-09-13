/* Keep sand lettering as compact as the portrait-phone reference at every size. */
(function(host){
  'use strict';
  const clamp=(v,a,b)=>Math.max(a,Math.min(b,v));
  function scale(width,height){
    if(!(Number.isFinite(width)&&Number.isFinite(height)&&width>0&&height>0))return 1;
    const aspect=width/height,t=clamp((aspect-1)/.3,0,1),wide=t*t*(3-2*t);
    // The existing renderer grows grains with viewport height. Compensate only
    // for the remaining difference in projected letter size from 390 × 844.
    const referenceSpan=390*.84,referenceGrain=844/800;
    const span=Math.min(.68,aspect*.84)*height;
    const grain=clamp(height/800,1,1.4);
    return 1+wide*(Math.max(1,span/referenceSpan*referenceGrain/grain)-1);
  }
  function create(count){
    const masks=new WeakMap(),zero=new Float32Array(count),attributes=new Float32Array(count*2);
    let previousFrom=null,previousTo=null;
    const get=positions=>masks.get(positions)||zero;
    return {
      attributes,
      mark(positions,weights){masks.set(positions,weights||new Float32Array(count).fill(1));},
      capture(from,to,amount,result){
        const a=get(from),b=get(to);if(a===zero&&b===zero)return;
        const weights=new Float32Array(count);
        for(let i=0;i<count;i++)weights[i]=a[i]+(b[i]-a[i])*amount;
        masks.set(result,weights);
      },
      update(from,to){
        const a=get(from),b=get(to);if(a===previousFrom&&b===previousTo)return false;
        previousFrom=a;previousTo=b;
        for(let i=0;i<count;i++){attributes[i*2]=a[i];attributes[i*2+1]=b[i];}
        return true;
      }
    };
  }
  host.CourseOpeningInscription=Object.freeze({scale,create});
})(typeof window!=='undefined'?window:globalThis);
