// Spend the mobile pixel budget on edges and text before optional glow effects.
export function displayProfile(width,height,dpr=1,quality='high',maxSamples=4,nativeSamples=4,device={}){
  width=Math.max(1,width);height=Math.max(1,height);
  const compact=Math.min(width,height)<=700,high=quality==='high';
  const mobile=Boolean(device.mobile),safe=Boolean(device.safe);
  const budget=mobile?(safe?650000:high?1200000:850000):high?(compact?3500000:6000000):2200000;
  const pixelRatio=Math.min(Math.max(1,dpr||1),(mobile?(safe?1.25:2):high?3:1.75),Math.sqrt(budget/(width*height)));
  return {compact,pixelRatio,samples:Math.max(0,Math.min(high?4:2,maxSamples)),direct:mobile||nativeSamples>0,bloom:false,shadows:high&&!safe,shadowSize:mobile||compact?1024:2048};
}
export function boardFraming(aspect,fov=57){
  const tangent=Math.tan(fov*Math.PI/360);
  // Frame the active board, not the whole two-board wall, in portrait view.
  const distance=Math.max(2.5/(2*tangent*.72),5.65/(2*tangent*Math.max(.2,aspect)*.9));
  return {distance:aspect<1?distance:Math.max(5,distance),single:aspect<1};
}
export function readingFormulaWidth(em,fontSize=24){return Math.max(40,em*Math.max(18,Math.min(36,fontSize)));}
