export function acceptsStartupQuality(frames,gpu=[],targetFPS=60){
 if(frames.length<12)return false;
 const sorted=frames.filter(Number.isFinite).sort((a,b)=>a-b),budget=1000/Math.min(60,Math.max(30,targetFPS));
 if(sorted.length<12)return false;
 const p90=sorted[Math.ceil(sorted.length*.9)-1],median=sorted[Math.floor(sorted.length/2)];
 const gpuSorted=gpu.filter(Number.isFinite).sort((a,b)=>a-b),gpu90=gpuSorted.length?gpuSorted[Math.ceil(gpuSorted.length*.9)-1]:null;
 return median<=budget*1.15&&p90<=budget*1.5&&(gpu90===null||gpu90<budget*.85);
}
