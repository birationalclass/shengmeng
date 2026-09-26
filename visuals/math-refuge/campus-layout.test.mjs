import fs from 'node:fs';
import assert from 'node:assert/strict';
const base=new URL('./',import.meta.url);
let code=fs.readFileSync(new URL('campus-layout.js',base),'utf8').replaceAll("from 'three'",`from '${new URL('../3d/vendor/three.module.js',base)}'`).replace(/from '(\.\/[^']+)'/g,(_,p)=>`from '${new URL(p,base)}'`);
const m=await import('data:text/javascript;base64,'+Buffer.from(code).toString('base64'));
const T=await import(new URL('../3d/vendor/three.module.js',base));
const {bridgePlan}=await import('./campus-plan.js');
const {BUILDING_SCALE:S}=await import('./site-layout.js');
const scene=new T.Scene(),hall=new T.Mesh(new T.BoxGeometry(1,1,1),new T.MeshStandardMaterial());
hall.position.set(39*S,2,0);scene.add(hall);m.relocateArchitecture(scene,[hall]);
const rooms=[{root:new T.Group()},{root:new T.Group()}];
const mat=new T.MeshStandardMaterial();m.finishCampusLayout(scene,{site:{seaLevel:-1},materials:{edge:mat,stone:mat,timber:mat}},rooms);
assert.ok(Math.abs(hall.position.x-(39*S-30))<1e-8);assert.equal(hall.position.z,0);
assert.equal(rooms[0].root.position.x,-30);
for(const b of m.campusLayout){const r=bridgePlan.buildings.find(r=>r.id===b[0]);assert.equal(b[4],r.east);assert.equal(b[5],r.north);}
const bridges=scene.getObjectByName('September 26 campus bridges');assert.equal(bridges.children.length,21);
for(const deck of bridges.children)assert.ok(Math.abs(deck.position.y+.14-.275*S)<1e-8);
const shots=[{name:'报告厅',positions:[[39*S,2,0]],targets:[[42*S,2,0]]}];m.relocateShots(shots);assert.equal(shots[0].positions[0][0],39*S-30);assert.equal(shots.length,5);
console.log('PASS: supplied coordinates, relocated hall/boards/camera, 15 spans + 6 garden decks, flush deck heights');

const stair=scene.getObjectByName('Hall southwest curved stair');assert.equal(stair.userData.steps,32);assert.ok(stair.userData.riser<.18);assert.equal(stair.children.filter(m=>m.name.startsWith('Curved timber tread')).length,32);assert.ok(stair.userData.exit[1]>stair.userData.entry[1]+5);console.log('PASS: 32 curved treads, riser below 18cm and south-to-west rise');

for(const axis of [0,2])assert.ok(Math.abs(stair.userData.entryLeft[axis]-stair.userData.southwestCorner[axis])<1e-9);console.log("PASS: entrance left edge exactly coincides with hall southwest corner");

assert.equal(stair.userData.landingBounds[1],stair.userData.upperSouthwestCorner[0]);assert.equal(stair.userData.landingBounds[3],stair.userData.upperSouthwestCorner[2]);assert.equal(stair.userData.landingCorner[1],stair.userData.exit[1]);console.log('PASS: upper landing shares exact west/south wall coordinates');
