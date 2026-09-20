import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../../3d/vendor/three.module.js';
import {gearTrain,clockworkCity} from '../clockwork.mjs';
import {replaceDomain,enrichDomain} from '../enchanted-domains.mjs';
import {dollyRadius,cameraKey} from '../camera-navigation.mjs';
import {SudokuAtlas} from '../atlas.mjs';
import {AtlasScene} from '../../test-module/scene.mjs';
function builder(){const a=Object.create(AtlasScene.prototype);a.materials=Object.fromEntries(['stone','paper','dark','gold','wood','jade','brass','red'].map(n=>[n,new T.MeshStandardMaterial()]));a.rotating=[];a.detailMotion=[];return a;}
test('gears touch at pitch radii and every meshing pair has equal opposite tangential velocity',()=>{const gears=gearTrain();for(let i=1;i<gears.length;i++){const a=gears[i-1],b=gears[i];assert.ok(Math.abs(b.x-a.x-a.radius-b.radius)<1e-9);assert.ok(Math.abs(a.radius*a.speed+b.radius*b.speed)<1e-9);}});
test('dolly is stable across frame rates, bounded, and Shift retains cell navigation',()=>{const advance=rate=>{let r=100;for(let i=0;i<rate;i++)r=dollyRadius(r,1,1/rate);return r;};assert.ok(Math.abs(advance(30)-advance(120))<1e-9);assert.ok(dollyRadius(100,1,.03)<100);assert.ok(dollyRadius(100,-1,.03)>100);assert.equal(dollyRadius(16,1,1),16);assert.equal(dollyRadius(230,-1,1),230);assert.ok(cameraKey({key:'ArrowUp'}));assert.ok(!cameraKey({key:'ArrowUp',shiftKey:true}));});
test('rigid board rises monotonically without compressing its surface',()=>{const object=new T.Group(),part={object,position:new T.Vector3(0,.8,0),scale:new T.Vector3(1,1,1),delay:2.05,duration:1.2,lift:2.2,rigid:true},state={boards:[{parts:[part]}]};let last=-Infinity;for(let t=0;t<4;t+=.05){SudokuAtlas.prototype.assemble.call(state,0,t);assert.ok(object.position.y>=last);assert.deepEqual(object.scale.toArray(),[1,1,1]);last=object.position.y;}assert.equal(last,.8);});
test('new landmarks leave the board volume clear and have finite geometry',()=>{for(const index of [0,1,2,3,4,5,6,7]){const a=builder(),p=new T.Group();replaceDomain(a,p,index);enrichDomain(a,p,index);p.updateMatrixWorld(true);let count=0;p.traverse(o=>{if(!o.isMesh)return;count++;assert.ok(o.matrixWorld.elements.every(Number.isFinite));const point=o.getWorldPosition(new T.Vector3());if(index!==2||!['CylinderGeometry','TorusGeometry'].includes(o.geometry.type))assert.ok(Math.abs(point.x)>5.9||Math.abs(point.z)>5.9,`domain ${index}: decoration intrudes at ${point.toArray()}`);});assert.ok(count>5);}});
