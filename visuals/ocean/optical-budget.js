// Experiment 02 only. Scores describe resource budgets, never visual fidelity
// or an unavailable OS-wide CPU/GPU utilization percentage.
export const presets={
  eco:{name:'节能',fps:30,pixels:650000,quality:'low',bands:5,particles:.45},
  balanced:{name:'均衡',fps:60,pixels:950000,quality:'balanced',bands:7,particles:.72},
  fine:{name:'精细',fps:60,pixels:1500000,quality:'fine',bands:9,particles:1}
};
export function percentile(values,p=.95){if(!values.length)return null;const a=[...values].sort((x,y)=>x-y);return a[Math.min(a.length-1,Math.floor((a.length-1)*p))];}
export function resourceScore({fps,cpu,gpu,pixels,triangles,target}){
  const clamp=x=>Math.max(0,Math.min(1,x));
  const smooth=clamp(fps/target), cpuHeadroom=1-clamp(cpu*target/1000);
  const gpuHeadroom=gpu==null?null:1-clamp(gpu*target/1000);
  // Submitted pixels + triangles per second; explicitly a workload proxy.
  const work=1-clamp((pixels*target+triangles*target)/180000000);
  const weight=gpuHeadroom==null?75:100;
  return Math.round(100*(smooth*40+cpuHeadroom*15+work*20+(gpuHeadroom??0)*25)/weight);
}
export function bufferBytes(scene){
  const arrays=new Set();scene.traverse(o=>{const g=o.geometry;if(!g)return;for(const a of Object.values(g.attributes))arrays.add(a.array);if(g.index)arrays.add(g.index.array);});
  return [...arrays].reduce((n,a)=>n+a.byteLength,0);
}
