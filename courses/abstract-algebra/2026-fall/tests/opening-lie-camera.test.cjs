const assert=require('node:assert/strict');global.window=global;
require('../opening-camera.js');require('../opening-timeline.js');
const C=CourseOpeningCamera;
C.setFocuses(Array.from({length:10},()=>[.3,-.2,.1]));
for(const ids of [[3],[3,4],[4,3],[8,3,5]])for(const phaseOffset of [0,.37]){
  const holds=ids.map(()=>30000),transitions=ids.map(()=>10000);
  const timeline=CourseOpeningTimeline.create({holds,transitions});
  let span=0;const starts=holds.map((hold,i)=>{const start=span;span+=hold+transitions[i];return start;});
  const route={holds,transitions,starts,duration:timeline.duration,phaseOffset,sceneIds:ids};
  const pose=t=>{const s=timeline.seek(t);return C.sampleTimeline({...s,scene:ids[s.scene],from:ids[s.from],to:ids[s.to]},route);};
  let minRoll=Infinity,maxRoll=-Infinity,maxZoom=1;
  for(let t=0;t<timeline.duration;t+=100){
    const s=timeline.seek(t),view=pose(t);
    assert.ok(view.zoom>=1&&view.zoom<=1.600001);
    if(ids[s.from]===3&&ids[s.to]===3||!s.moving&&ids[s.scene]===3){
      assert.equal(view.zoom,1.6,'Lie-group framing stays at 160% for the entire hold');assert.deepEqual(view.target,[0,0,0]);
      maxZoom=Math.max(maxZoom,view.zoom);
      assert.equal(view.angles[0],C.neutral.angles[0]);assert.equal(view.angles[1],0);
      assert.ok(Math.abs(view.angles[2])<=8*Math.PI/180+1e-12);
      minRoll=Math.min(minRoll,view.angles[2]);maxRoll=Math.max(maxRoll,view.angles[2]);
    }
    timeline.setDirection(-1);assert.deepEqual(pose(t),view,'reverse traces the same camera');timeline.setDirection(1);
  }
  assert.ok(maxRoll-minRoll>.01,'the Z-axis camera remains gently moving');
  assert.ok(Math.abs(maxZoom-1.6)<1e-12,'each Lie-group viewing interval reaches the requested 160%');
  for(const boundary of [...starts,...starts.map((start,i)=>start+holds[i]),timeline.duration]){
    const left=pose(boundary-.001),right=pose(boundary+.001);
    for(const key of ['angles','target'])left[key].forEach((v,i)=>assert.ok(Math.abs(v-right[key][i])<1e-6,'no transition or loop seam jump'));
    assert.ok(Math.abs(left.zoom-right.zoom)<1e-6);
  }
}
assert.deepEqual(C.sample(3,.5,[.4,-.7,.2]).target,[0,0,0]);
console.log('PASS: Lie-group zoom stays within 1x–1.6x, bounded Z-axis motion, reverse/custom order/single-scene loops and smooth joins');
