import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../../3d/vendor/three.module.js';
import {gearTrain,clockworkCity} from '../clockwork.mjs';
import {replaceDomain,enrichDomain} from '../enchanted-domains.mjs';
import {dollyRadius,cameraKey} from '../camera-navigation.mjs';
import {SudokuAtlas} from '../atlas.mjs';
import {AtlasScene} from '../../test-module/scene.mjs';
function builder(){const a=Object.create(AtlasScene.prototype);a.materials=Object.fromEntries(['stone','paper','dark','gold','wood','jade','brass','red'].map(n=>[n,new T.MeshStandardMaterial()]));a.rotating=[];a.detailMotion=[];return a;}
test('arrows pan N/S/W/E without zoom or rotation, independent of orbit and frame rate',()=>{
 const move=(rate,east,north,theta=0)=>{const state={manual:{target:new T.Vector3(),radius:40,theta,phi:.7},touring:true};for(let i=0;i<rate;i++)SudokuAtlas.prototype.pan.call(state,east,north,1/rate);return state;};
 for(const [east,north,x,z]of [[1,0,12,0],[-1,0,-12,0],[0,1,0,-12],[0,-1,0,12]]){const a=move(60,east,north),b=move(30,east,north,1.3);assert.ok(a.manual.target.distanceTo(new T.Vector3(x,0,z))<1e-9);assert.ok(a.manual.target.distanceTo(b.manual.target)<1e-9);assert.equal(a.manual.radius,40);assert.equal(a.manual.phi,.7);assert.equal(b.manual.theta,1.3);}
 assert.ok(Math.abs(move(60,1,1).manual.target.length()-12)<1e-9);
 const state=move(60,1,0),target=state.manual.target.clone();SudokuAtlas.prototype.pan.call(state,0,0,.05);assert.deepEqual(state.manual.target,target);state.sequence={};SudokuAtlas.prototype.pan.call(state,1,1,.05);assert.deepEqual(state.manual.target,target);
 for(const key of ['ArrowLeft','ArrowRight','ArrowUp','ArrowDown']){assert.ok(cameraKey({key}));assert.ok(!cameraKey({key,shiftKey:true}));assert.ok(!cameraKey({key,metaKey:true}));}
});
test('gears touch at pitch radii and every meshing pair has equal opposite tangential velocity',()=>{const gears=gearTrain();for(let i=1;i<gears.length;i++){const a=gears[i-1],b=gears[i];assert.ok(Math.abs(b.x-a.x-a.radius-b.radius)<1e-9);assert.ok(Math.abs(a.radius*a.speed+b.radius*b.speed)<1e-9);}});
test('dolly is stable across frame rates, bounded, and Shift retains cell navigation',()=>{const advance=rate=>{let r=100;for(let i=0;i<rate;i++)r=dollyRadius(r,1,1/rate);return r;};assert.ok(Math.abs(advance(30)-advance(120))<1e-9);assert.ok(dollyRadius(100,1,.03)<100);assert.ok(dollyRadius(100,-1,.03)>100);assert.equal(dollyRadius(16,1,1),16);assert.equal(dollyRadius(230,-1,1),230);assert.ok(cameraKey({key:'ArrowUp'}));assert.ok(!cameraKey({key:'ArrowUp',shiftKey:true}));});
test('rigid board rises monotonically without compressing its surface',()=>{const object=new T.Group(),part={object,position:new T.Vector3(0,.8,0),scale:new T.Vector3(1,1,1),delay:2.05,duration:1.2,lift:2.2,rigid:true},state={boards:[{parts:[part]}]};let last=-Infinity;for(let t=0;t<4;t+=.05){SudokuAtlas.prototype.assemble.call(state,0,t);assert.ok(object.position.y>=last);assert.deepEqual(object.scale.toArray(),[1,1,1]);last=object.position.y;}assert.equal(last,.8);});
test('new landmarks leave the board volume clear and have finite geometry',()=>{for(const index of [0,1,2,3,4,5,6,7]){const a=builder(),p=new T.Group();replaceDomain(a,p,index);enrichDomain(a,p,index);p.updateMatrixWorld(true);let count=0;p.traverse(o=>{if(!o.isMesh)return;count++;assert.ok(o.matrixWorld.elements.every(Number.isFinite));const bounds=new T.Box3().setFromObject(o),usable=new T.Box3(new T.Vector3(-5.6,1.4,-5.6),new T.Vector3(5.6,2.3,5.6));assert.ok(!bounds.intersectsBox(usable),`domain ${index}: decoration intrudes into board volume`);});assert.ok(count>5);}});
