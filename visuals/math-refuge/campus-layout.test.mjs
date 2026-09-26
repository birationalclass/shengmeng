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
const mat=new T.MeshStandardMaterial();m.finishCampusLayout(scene,{site:{seaLevel:-1},materials:{edge:mat,stone:mat,timber:mat,terraceFloor:mat,brass:mat,steel:mat,light:mat,glass:mat}},rooms);
assert.ok(Math.abs(hall.position.x-(39*S-30))<1e-8);assert.equal(hall.position.z,0);
assert.equal(rooms[0].root.position.x,-30);
for(const b of m.campusLayout){const r=bridgePlan.buildings.find(r=>r.id===b[0]);assert.equal(b[4],r.east);assert.equal(b[5],r.north);}
const bridges=scene.getObjectByName('September 26 campus bridges');assert.equal(bridges.children.length,19);
for(const deck of bridges.children){if(deck.isGroup){deck.updateMatrixWorld(true);const bounds=new T.Box3().setFromObject(deck);assert.ok(Math.abs(bounds.max.y-.275*S)<1e-5);assert.equal(deck.userData.curved,true);assert.equal(deck.userData.stoneDeck,true);}else assert.ok(Math.abs(deck.position.y+.14-.275*S)<1e-8);}
const shots=[{name:'报告厅',positions:[[39*S,2,0]],targets:[[42*S,2,0]]}];m.relocateShots(shots);assert.equal(shots[0].positions[0][0],39*S-30);assert.equal(shots.length,5);
console.log('PASS: supplied coordinates, relocated hall/boards/camera, 13 spans + 6 garden decks, flush deck heights');

const stair=scene.getObjectByName('Hall southwest curved stair');assert.equal(stair.userData.steps,32);assert.ok(stair.userData.riser<.18);assert.equal(stair.children.filter(m=>m.name.startsWith('Curved timber tread')).length,32);assert.ok(stair.userData.exit[1]>stair.userData.entry[1]+5);console.log('PASS: 32 curved treads, riser below 18cm and south-to-west rise');

for(const axis of [0,2])assert.ok(Math.abs(stair.userData.entryLeft[axis]-stair.userData.southwestCorner[axis])<1e-9);console.log("PASS: entrance left edge exactly coincides with hall southwest corner");

assert.equal(stair.userData.landingBounds[1],stair.userData.upperSouthwestCorner[0]);assert.equal(stair.userData.landingBounds[3],stair.userData.upperSouthwestCorner[2]);assert.equal(stair.userData.landingCorner[1],stair.userData.exit[1]);console.log('PASS: upper landing shares exact west/south wall coordinates');

const landing=stair.getObjectByName('Landing continuous terrace floor');assert.equal(landing.material[2],mat);assert.ok(Math.abs(landing.geometry.parameters.width-1.675)<1e-8);assert.ok(Math.abs(landing.position.y+landing.geometry.parameters.height/2-stair.userData.exit[1])<1e-9);console.log('PASS: trimmed landing shares terrace material and exact floor height');

assert.ok(Math.abs(landing.geometry.parameters.height-.475*S)<1e-9);assert.equal(stair.children.filter(m=>m.name==='Landing perimeter light strip').length,3);console.log('PASS: matching platform thickness and three exposed lit edges');

assert(!bridgePlan.connections.flat().includes('01C'));
const furniture=scene.getObjectByName('Hall terrace B sea conversation');assert(furniture);assert.equal(furniture.userData.chairs,8);assert.equal(furniture.children.filter(o=>o.name==='Terrace timber armchair').length,8);
const pavilion=scene.getObjectByName('Hall sea promenade and pavilion');assert.equal(pavilion.userData.dimensions.scheme,'A');assert.equal(pavilion.userData.dimensions.pavilionYaw,0);
console.log('PASS: scheme B eight outdoor chairs, scheme A aligned pavilion, isolated backup hall');
