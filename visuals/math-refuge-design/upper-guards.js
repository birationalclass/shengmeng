import {platformUnion} from './platform-union.js';
export function perimeterRails(rectangles,openings=[]){
  const segments=[];
  for(const [x1,z1,x2,z2] of platformUnion(rectangles).edges){
    const axis=z1===z2?'x':'z',fixed=axis==='x'?z1:x1;
    let intervals=[[Math.min(axis==='x'?x1:z1,axis==='x'?x2:z2),Math.max(axis==='x'?x1:z1,axis==='x'?x2:z2)]];
    for(const gap of openings.filter(g=>g.axis===axis&&Math.abs(g.fixed-fixed)<1e-7)){
      intervals=intervals.flatMap(([a,b])=>gap.to<=a||gap.from>=b?[[a,b]]:[[a,Math.max(a,gap.from)],[Math.min(b,gap.to),b]].filter(([c,d])=>d-c>1e-7));
    }
    for(const [a,b] of intervals)segments.push(axis==='x'?[a,fixed,b,fixed]:[fixed,a,fixed,b]);
  }
  return segments;
}
