const assert=require('node:assert/strict');global.window=global;
require('../opening-galois-story.js');require('../opening-timeline.js');
const S=CourseOpeningGaloisStory;
for(const hold of [30000,45000,60000,90000])for(const speed of [.25,.5,.75,1,1.5]){
 const morph=5000/speed,duration=S.duration(hold,morph);assert.equal(duration,7*hold+6*morph);
 for(let i=0;i<7;i++){
  const start=i*(hold+morph);assert.equal(S.state(start+hold/2,hold,morph).node,i);
  if(i<6){const time=start+hold+morph*.37,state=S.state(time,hold,morph);assert(state.moving);assert.equal(state.from,i);assert.equal(state.to,i+1);assert(Math.abs(state.progress-.37)<1e-12);
   const next=S.state(S.remap(time,hold,morph,hold*1.5,morph/2),hold*1.5,morph/2);assert.equal(next.from,i);assert(Math.abs(next.progress-.37)<1e-12);
  }
 }
 const T=CourseOpeningTimeline.create({holds:[duration],transitions:[13500],morphSingle:true});
 assert.equal(T.seek(duration+6750).moving,true);assert.equal(T.state().progress,.5);
 T.setDirection(-1);T.advance(6750);assert.equal(T.state().progress,0);T.advance(1);assert.equal(T.state().moving,false);
}
assert.match(S.nodes[4].year,/29 MAY/);assert.match(S.nodes[5].en,/May 30/);assert.match(S.nodes[5].en,/May 31/);assert.match(S.nodes[6].year,/1843.*1846/);
console.log('PASS: seven complete independent holds, additional morph time, reversible single-story loop and exact phase preservation during timing edits');

for(const [t,node] of [[25000,2],[74000,3],[100000,4],[128000,5],[167000,6]]){
 const a=S.state(t,30000,10000,true);assert.equal(a.node,node);assert.equal(a.moving,false);
}
assert.equal(S.duration(30000,10000,true),177160.612);
for(const t of [4000,20000,80000,121000,137000,167000]){
 const a=S.state(t,30000,10000,true),b=S.state(S.remap(t,30000,10000,45000,7000,true,false),45000,7000,false);
 assert.equal(a.from,b.from);assert.equal(a.to,b.to);assert(Math.abs(a.progress-b.progress)<1e-10);
}
console.log('PASS: music landmarks land on the intended tableaux; scored/manual timing changes preserve the current formation');
