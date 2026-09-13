const assert=require('node:assert/strict');global.window=global;require('../opening-motion.js');
let seed=317129;const grains=new Float32Array(72000*4);
for(let i=0;i<grains.length;i++){seed=(Math.imul(seed,1664525)+1013904223)>>>0;grains[i]=seed/4294967296;}
for(const [width,height] of [[1280,900],[1920,1080],[3440,1440],[390,844],[320,740],[844,390]]){
 const points=CourseOpeningMotion.entrancePositions(grains,width,height),aspect=width/height,fit=Math.min(.68,aspect*.84),t=Math.max(0,Math.min(1,(aspect-.8)/.5)),centre=.05+.15*t*t*(3-2*t),edges=[0,0,0,0];
 assert.equal(points.length,72000*3);
 for(let i=0;i<points.length;i+=3){
  const x=points[i]*fit/aspect,y=points[i+1]*fit+centre,extent=Math.max(Math.abs(x),Math.abs(y));
  assert.ok(extent>=1.07999&&extent<=1.63001,'every particle starts beyond the visible rectangle');
  assert.equal(points[i+2],0);
  edges[Math.abs(x)>Math.abs(y)?x>0?0:1:y>0?2:3]++;
 }
 assert.ok(edges.every(n=>n>16000),'sand arrives from all four edges');
}
console.log('PASS: 72,000 grains begin outside all desktop/mobile/fullscreen viewports, spread across four edges');
