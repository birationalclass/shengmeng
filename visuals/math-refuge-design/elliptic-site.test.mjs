import test from 'node:test';
import assert from 'node:assert/strict';
import {CAMPUS_ANCHOR,COAST_LIFT,toBeach,fromBeach,beachDistance,campusGround,toMathCoordinates} from './elliptic-site.js';
import {RESIDENCE,RESIDENCE_SHOTS} from './residence-layout.js';
import {BUILDING_SCALE as S,HALL} from './site-layout.js';
import {SHOTS} from './camera-paths.js';
import {branchPoint,ringPoint} from '../ocean/elliptic-model.js';
test('main auditorium is exactly at elliptic coordinate (2 km, 0 km)',()=>{
 assert.equal(CAMPUS_ANCHOR,(HALL.west+HALL.east)*.5*S);
 assert.deepEqual(toBeach(CAMPUS_ANCHOR,0),[2000,0]);
 for(const p of [[0,0],[500,-380],[2000,0],[4500,6000]]){
  const q=toBeach(...fromBeach(...p));q.forEach((v,i)=>assert(Math.abs(v-p[i])<1e-9));
 }
 assert(2.83+COAST_LIFT<.28*S,'highest demonstration tide stays below occupied decks');
});
test('full ring and branch terrain samples agree with the shared 01 geometry',()=>{
 for(let i=0;i<=100;i++)for(const point of [ringPoint(i*Math.PI/50),branchPoint(-1.7+3.4*i/100)])assert(beachDistance(...point)<.08);
 for(const t of [-1.7,1.7])assert(Math.abs(campusGround(...fromBeach(...branchPoint(t)))-(-18+COAST_LIFT))<1e-8);
});
test('residence follows the sand ridge and its room cameras move with the building',()=>{
 assert(beachDistance(...toBeach(RESIDENCE.origin[0],RESIDENCE.origin[2]))<.02);
 const entry=RESIDENCE_SHOTS.find(s=>s.name==='住宅玄关');
 assert(Math.abs(entry.positions[0][2]*S-RESIDENCE.origin[2]-12)<1e-8);
 assert(Math.abs(entry.positions[0][0]*S-RESIDENCE.origin[0]-3)<1e-8);
});
test('coast overview, loop and campus views are navigable and finite',()=>{
 for(const name of ['曲线海岸总览','左环漫滩','主楼沙滩']){
  const shot=SHOTS.find(s=>s.name===name);assert(shot);
  for(const p of [...shot.positions,...shot.targets])assert(p.every(Number.isFinite));
 }
});

test('geographic east is +x and north is +y in kilometre coordinates',async()=>{
 const {geographicDirectionToCampus,toMathCoordinates}=await import('./elliptic-site.js');
 const anchor=fromBeach(2000,0);
 for(const [direction,expected] of [[[1,0,0],[3,0]],[[0,0,-1],[2,1]]]){
  const v=geographicDirectionToCampus(direction);
  const p=toMathCoordinates(anchor[0]+v[0]*1000,anchor[1]+v[2]*1000);
  p.forEach((value,i)=>assert(Math.abs(value-expected[i])<1e-9));
 }
 const shot=SHOTS.find(s=>s.name==='曲线海岸总览');
 // The camera approaches the zenith from geographic south, so screen-up is north.
 const eye=shot.positions[0],target=shot.targets[0];
 assert(eye[1]>5000);assert(eye[2]>target[2]);assert(Math.abs(eye[0]-target[0])<1e-8);
});

// Test against the host scene axes, not only two helpers that could share a rotation bug.
test('right-arm apex tangent points north in the actual scene frame',()=>{
 const p=fromBeach(...branchPoint(.0001)),origin=fromBeach(...branchPoint(0));
 const dx=p[0]-origin[0],dz=p[1]-origin[1];
 assert(dz<0);assert(Math.abs(dx/dz)<.001);
 const east=toMathCoordinates(CAMPUS_ANCHOR+1000,0),north=toMathCoordinates(CAMPUS_ANCHOR,-1000);
 assert.equal(east[0],3);assert(Math.abs(east[1])<1e-12);assert(Math.abs(north[0]-2)<1e-12);assert.equal(north[1],1);
});
