/* Keep sand lettering as compact as the portrait-phone reference at every size. */
(function(host){
  'use strict';
  const clamp=(v,a,b)=>Math.max(a,Math.min(b,v));
  function landscape(width,height){
    if(!(Number.isFinite(width)&&Number.isFinite(height)&&width>0&&height>0))return 0;
    const t=clamp((width/height-1)/.3,0,1);return t*t*(3-2*t);
  }
  function scale(width,height){
    if(!(Number.isFinite(width)&&Number.isFinite(height)&&width>0&&height>0))return 1;
    const aspect=width/height,wide=landscape(width,height);
    // The existing renderer grows grains with viewport height. Compensate only
    // for the remaining difference in projected letter size from 390 × 844.
    const referenceSpan=390*.84,referenceGrain=844/800;
    const span=Math.min(.68,aspect*.84)*height;
    const grain=clamp(height/800,1,1.4);
    return 1+wide*(Math.max(1,span/referenceSpan*referenceGrain/grain)-1);
  }
  // Small names and dates need finer sprites: 35% diameter gives roughly half the visible stroke weight.
  const signatureScale=(width,height)=>1-.65*landscape(width,height);
  function create(count){
    const masks=new WeakMap(),zero=new Float32Array(count),empty={text:zero,signature:zero},attributes=new Float32Array(count*4);
    let previousFrom=null,previousTo=null;
    const get=positions=>masks.get(positions)||empty;
    return {
      attributes,
      mark(positions,weights,signature=zero){masks.set(positions,{text:weights||new Float32Array(count).fill(1),signature});},
      capture(from,to,amount,result){
        const a=get(from),b=get(to);if(a===empty&&b===empty)return;
        const text=new Float32Array(count),signature=new Float32Array(count);
        for(let i=0;i<count;i++){text[i]=a.text[i]+(b.text[i]-a.text[i])*amount;signature[i]=a.signature[i]+(b.signature[i]-a.signature[i])*amount;}
        masks.set(result,{text,signature});
      },
      update(from,to){
        const a=get(from),b=get(to);if(a===previousFrom&&b===previousTo)return false;
        previousFrom=a;previousTo=b;
        for(let i=0;i<count;i++){attributes[i*4]=a.text[i];attributes[i*4+1]=b.text[i];attributes[i*4+2]=a.signature[i];attributes[i*4+3]=b.signature[i];}
        return true;
      }
    };
  }
  host.CourseOpeningInscription=Object.freeze({scale,signatureScale,create});
})(typeof window!=='undefined'?window:globalThis);
