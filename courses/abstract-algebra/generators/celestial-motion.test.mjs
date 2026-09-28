import test from 'node:test';import assert from 'node:assert/strict';
import {planetMotion,starMotion,PLANET_PERIODS,orbitalOffset,spreadStarOrbits} from './celestial-motion.mjs';
test('compressed periods remain distinct, repeatable and visibly animated',()=>{
 for(const type of Object.keys(PLANET_PERIODS)){const a=planetMotion(type,7),b=planetMotion(type,8);assert.deepEqual(a,planetMotion(type,7));assert.notEqual(a.spin,b.spin);assert.ok(a.orbitSeconds>8&&a.orbitSeconds<30);assert.ok(a.spinSeconds>4&&a.spinSeconds<14);}
 assert.ok(planetMotion('gas-planet',7).spin>planetMotion('ocean-planet',7).spin);
 assert.ok(planetMotion('ice-planet',7).orbit<planetMotion('gas-planet',7).orbit);
});
test('stars have stable randomized distances and prograde orbits',()=>{const radii=new Set();for(let i=0;i<120;i++){const s=starMotion(i);assert.ok(s.radius>=5&&s.radius<8);assert.ok(s.orbit>0);radii.add(s.radius);}assert.equal(radii.size,120);});

test('orbital planes have fixed bounded inclinations and preserve orbit radius',()=>{let positive=0,negative=0;for(let i=0;i<120;i++){const m=planetMotion('gas-planet',i);assert.ok(Math.abs(m.inclination)<=Math.PI/4);m.inclination>0?positive++:negative++;for(const a of [0,.7,2,4]){const p=orbitalOffset(m,a,3);assert.ok(Math.abs(Math.hypot(p.x,p.y,p.z)-3)<1e-10);const normal={x:-Math.sin(m.node)*Math.sin(m.inclination),y:Math.cos(m.inclination),z:-Math.cos(m.node)*Math.sin(m.inclination)};assert.ok(Math.abs(p.x*normal.x+p.y*normal.y+p.z*normal.z)<1e-10);}}assert.ok(positive>0&&negative>0);assert.notEqual(starMotion(1).spinTilt,starMotion(2).spinTilt);});

test('dense stellar systems occupy separated inner, middle and outer bands',()=>{const a=spreadStarOrbits(25,71);assert.deepEqual(a,spreadStarOrbits(25,71));assert.ok(a[0].radius<4.2);assert.ok(a.at(-1).radius>10.8);for(let i=1;i<a.length;i++)assert.ok(a[i].radius>a[i-1].radius);});

test('stellar orbits respect black-hole edge clearance',()=>{for(const size of [.3,.7,1.2]){const edge=8.5*1.35/2*size,star=size*.8;for(const m of spreadStarOrbits(25,71,edge*2.5+star))assert.ok(m.radius-star-edge>=edge*1.5);}});
test('planet spin doubles while revolution stays unchanged',()=>{for(const type of Object.keys(PLANET_PERIODS)){const m=planetMotion(type,7);assert.ok(Math.abs(m.spin*m.spinSeconds-4*Math.PI)<1e-10);assert.ok(Math.abs(m.orbit*m.orbitSeconds-2*Math.PI)<1e-10);}});

test('all stellar orbits remain in the accretion plane',()=>{for(let seed=0;seed<7;seed++){assert.equal(starMotion(seed).inclination,0);for(const m of spreadStarOrbits(25,seed))assert.equal(m.inclination,0);}assert.notEqual(planetMotion('gas-planet',7).inclination,0);});

test('all planets assigned to one host share a plane within 15 degrees',()=>{for(let host=0;host<120;host++){const a=planetMotion('gas-planet',1,0,host);assert.ok(Math.abs(a.inclination)<=Math.PI/12);for(let i=0;i<10;i++){const b=planetMotion('ocean-planet',i,i,host);assert.equal(a.inclination,b.inclination);assert.equal(a.node,b.node);}}});

import {systemStarOrbits,planetOrbitRadius} from './celestial-motion.mjs';
import {groups} from './model.mjs';
import {celestialLayout,bodyScale} from './celestial-rank.mjs';
test('shared orbital rule clears every black hole and planetary envelope at every phase',()=>{
 for(const [key,g] of Object.entries(groups)){
  const scale=bodyScale(g.table.length),layout=celestialLayout(g),stars=layout.filter(p=>p.rank.type.endsWith('star')),orbits=systemStarOrbits(layout,scale,71,0),edge=12*(8.5/22)*scale*3;
  assert.deepEqual(orbits,systemStarOrbits(layout,scale,71,0));
  for(let i=0;i<stars.length;i++){
   const m=orbits[i];assert.equal(m.inclination,0);assert.ok(m.radius-scale*2.4>=edge*2.5-1e-9,key);
   for(const p of layout.filter(p=>p.host===stars[i].element)){const radius=1.5*scale*p.rank.scale,r=planetOrbitRadius(scale*2.4,radius,p.element,0,p.slot);assert.ok(m.radius-r-radius*(p.rank.type==='ring-planet'?2.25:1.055)>edge,key);}
   for(let j=0;j<i;j++){assert.equal(m.orbit,orbits[j].orbit);assert.ok(Math.hypot(m.radius*Math.cos(m.phase)-orbits[j].radius*Math.cos(orbits[j].phase),m.radius*Math.sin(m.phase)-orbits[j].radius*Math.sin(orbits[j].phase))>=scale*6-1e-9,key);}
  }
  if(stars.length===1)assert.ok(orbits[0].radius<edge*3,key+' should remain compact');
 }
});
