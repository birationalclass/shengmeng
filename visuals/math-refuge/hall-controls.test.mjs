import assert from 'node:assert/strict';
import * as T from '../3d/vendor/three.module.js';
import {HALL,SEAT_ROWS,BUILDING_SCALE as S,DECK_Y,LECTERN_SHAFT_PLAN} from './site-layout.js';
import {createLecternLift} from './lectern-lift.js';
import {hallSunStart,sunViewRate} from './hall-sun-view.js';
import {solarState} from './solar-state.js';
import {apparentAltitude} from './solar-optics.js';
assert.equal((HALL.west+HALL.east)/2,SEAT_ROWS[1].x);
assert.ok((SEAT_ROWS[0].x-HALL.west)*S>5);
const scene=new T.Scene(),lectern={group:new T.Group()},mat=new T.MeshStandardMaterial();lectern.group.position.y=(DECK_Y+.028)*S;
const lift=createLecternLift(scene,lectern,mat,new T.Vector3(-30,0,0));
lift.toggle();for(let i=0;i<360;i++)lift.update(1/60);
const lid=scene.getObjectByName('Seamless retractable lectern floor lid'),[a,b,c,d]=LECTERN_SHAFT_PLAN;
assert.ok(Math.abs(lid.position.y+.012*S-(DECK_Y+.028)*S)<1e-10);
assert.ok(Math.abs(lid.position.x-((a+b)/2*S-30))<1e-10);
assert.equal(lid.material,mat);assert.ok(lectern.group.position.y+1.49<DECK_Y*S);
lift.toggle();for(let i=0;i<360;i++)lift.update(1/60);
assert.ok(Math.abs(lectern.group.position.y-(DECK_Y+.028)*S)<1e-10);
for(const month of [0,2,5,8,11])for(const physical of [true,false])for(const event of ['sunrise','sunset']){
 const date=new Date(Date.UTC(2026,month,21)),hour=hallSunStart(event,date,physical),state=solarState(hour,date),radius=state.radius*180/Math.PI*(physical?1:event==='sunrise'?3:2),alt=apparentAltitude(state.elevation);
 assert.ok(event==='sunrise'?alt+radius<-.15:alt-radius>.99);
}
assert.equal(sunViewRate(0),1);assert.equal(sunViewRate(5),30);for(let t=0;t<5;t+=.01)assert.ok(sunViewRate(t+.01)>=sunViewRate(t));
console.log('PASS: centered middle row, >5m rear clearance, reversible lift and flush lid, seasonal solar limb clearances, smooth 1–30x ramp');

// Exercise actual instance updates without depending on the rounded-box shape in Node.
import fs from 'node:fs';
let chairCode=fs.readFileSync(new URL('./swivel-chairs.js',import.meta.url),'utf8');
chairCode=chairCode.replace("from 'three'",`from '${new URL('../3d/vendor/three.module.js',import.meta.url)}'`).replace(/import \{RoundedBoxGeometry\} from '[^']+';/,"class RoundedBoxGeometry extends T.BoxGeometry {constructor(w,h,d){super(w,h,d);}}");
const {createSwivelChairs}=await import('data:text/javascript;base64,'+Buffer.from(chairCode).toString('base64'));
const chairScene=new T.Scene(),geometry=new T.BoxGeometry(.1,.1,.1),chairs=createSwivelChairs(chairScene,[[36.2,0,0],[37.7,0,0],[39.2,0,0]],{shell:mat,cloth:mat,metal:mat,timber:mat,backs:[geometry]},S);
const upper=chairScene.getObjectByName('Rotating chair upper assembly'),before=new T.Matrix4(),after=new T.Matrix4();upper.getMatrixAt(1,before);
chairs.setSunsetDirection([-1,0,0],true);for(let i=0;i<1200;i++)chairs.update(1/60);
upper.getMatrixAt(1,after);assert.deepEqual(after.elements,before.elements);
upper.getMatrixAt(0,after);const facing=new T.Vector3(0,0,1).transformDirection(after);assert.ok(facing.x<-.99);
assert.equal(chairs.targets.length,0);
console.log('PASS: rear-row instances turn toward sunset; other rows and mouse non-interactivity remain unchanged');

