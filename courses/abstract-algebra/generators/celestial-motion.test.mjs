import test from 'node:test';import assert from 'node:assert/strict';
import {planetMotion,starMotion,PLANET_PERIODS} from './celestial-motion.mjs';
test('compressed periods remain distinct, repeatable and visibly animated',()=>{
 for(const type of Object.keys(PLANET_PERIODS)){const a=planetMotion(type,7),b=planetMotion(type,8);assert.deepEqual(a,planetMotion(type,7));assert.notEqual(a.spin,b.spin);assert.ok(a.orbitSeconds>8&&a.orbitSeconds<30);assert.ok(a.spinSeconds>4&&a.spinSeconds<14);}
 assert.ok(planetMotion('gas-planet',7).spin>planetMotion('ocean-planet',7).spin);
 assert.ok(planetMotion('ice-planet',7).orbit<planetMotion('gas-planet',7).orbit);
});
test('stars have stable randomized distances and prograde orbits',()=>{const radii=new Set();for(let i=0;i<120;i++){const s=starMotion(i);assert.ok(s.radius>=5&&s.radius<8);assert.ok(s.orbit>0);radii.add(s.radius);}assert.equal(radii.size,120);});
