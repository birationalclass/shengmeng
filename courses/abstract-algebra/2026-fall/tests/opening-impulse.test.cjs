const assert=require('node:assert/strict');global.window=global;require('../opening-impulse.js');
const I=CourseOpeningImpulse,impulse=I.create();
impulse.trigger([0,0,0],.45,10);
assert.deepEqual(impulse.offset([.1,0,0],10),[0,0,0]);
const near=impulse.offset([.1,0,0],10.2),far=impulse.offset([.7,0,0],10.2);
assert.ok(near[0]>.1&&near[0]>far[0]*10,'fast outward motion decays with distance');
assert.ok(impulse.offset([-.1,0,0],10.2)[0]<0,'direction points away from the click');
assert.ok(Math.hypot(...impulse.offset([0,0,0],10.2,.3))>.1,'centre grains disperse too');
assert.deepEqual(impulse.offset([.1,0,0],12),[0,0,0]);assert.equal(impulse.active(12),false);
assert.ok(Math.hypot(...impulse.offset([.1,0,0],11.65))<.002,'gentle final return');
for(let i=0;i<8;i++)impulse.trigger([i*.1,0,0],.3,12+i*.01);
assert.equal(impulse.evidence().length,4);assert.equal(impulse.uniforms().values.length,16);
impulse.clear();assert.equal(impulse.active(12.2),false);
// At the neutral camera, release location and radius map exactly to screen size.
for(const [width,height] of [[1280,900],[320,740]])for(const zoom of [1,5,10]){
 const aspect=width/height,fit=Math.min(.68,aspect*.84)*zoom,t=Math.max(0,Math.min(1,(aspect-.8)/.5)),centre=.05+.15*t*t*(3-2*t);
 const x=width*.37,y=height*.63,p=I.fromScreen(x,y,width,height,{angles:[0,0,0],target:[0,0,0],zoom},0);
 assert.ok(Math.abs((p.origin[0]*fit/aspect+1)*width/2-x)<1e-8);
 assert.ok(Math.abs((1-p.origin[1]*fit-centre)*height/2-y)<1e-8);
 assert.ok(Math.abs(p.radius*zoom-.45)<1e-12);
}
console.log('PASS: click-centred impulse; rapid distance-weighted dispersal; complete smooth recovery; four bounded overlapping pulses; zoom-correct pointer mapping');
