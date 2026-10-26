import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import * as T from '../3d/vendor/three.module.js';
import {HALL_CAMERA_BOUNDS as b,constrainHallCamera,hallOverview} from './blackboard-camera.js';
import {boardCameraFrame} from './board-camera-framing.js';
import {configureLectureRoot} from './site-layout.js';

function inside(p){assert(p.x>=b.minX&&p.x<=b.maxX);assert(p.y>=b.minY&&p.y<=b.maxY);assert(p.z>=b.minZ&&p.z<=b.maxZ);}
test('orbit, pan, dolly and keyboard candidates are constrained on every room face',()=>{
 const c=new T.PerspectiveCamera(57,1,.06,75),target=new T.Vector3();
 for(const x of [-1e6,b.minX,53,b.maxX,1e6])for(const y of [-1e6,2,1e6])for(const z of [-1e6,0,1e6]){
  c.position.set(x,y,z);target.copy(c.position).add(new T.Vector3(3,-1,2));constrainHallCamera(c,target);inside(c.position);assert(target.toArray().every(Number.isFinite));assert(c.quaternion.toArray().every(Number.isFinite));assert(c.position.distanceTo(target)>.009);
 }
});
test('nonfinite input recovers to a valid indoor position',()=>{const c=new T.PerspectiveCamera(),target=new T.Vector3(Infinity,NaN,-Infinity);c.position.set(NaN,Infinity,-Infinity);constrainHallCamera(c,target);inside(c.position);assert(target.toArray().every(Number.isFinite));});
test('all columns and board zooms retain their existing framing within the hall on desktop and phone',()=>{
 const root=new T.Group();configureLectureRoot(root);
 for(const aspect of [390/844,844/390,16/9])for(let column=0;column<3;column++)for(const zoom of [-.3,0,.5,1]){
  const f=boardCameraFrame(aspect,57,zoom,{column}),c=new T.PerspectiveCamera(f.fov,aspect,.06,75),target=root.localToWorld(new T.Vector3(f.x,f.y,f.z));c.position.copy(root.localToWorld(new T.Vector3(f.x,f.y,f.z+f.distance)));const before=c.position.clone();constrainHallCamera(c,target);inside(c.position);assert(before.distanceTo(c.position)<1e-9,'automatic board framing must not hit the room clamp');
 }
});
test('overview is inside the hall for landscape and portrait displays',()=>{for(const aspect of [.46,1,1.78,2.2]){const p=hallOverview(aspect),c=new T.PerspectiveCamera();c.position.fromArray(p.position);const t=new T.Vector3().fromArray(p.target);constrainHallCamera(c,t);inside(c.position);}});
test('standalone bundle excludes campus, ocean and outdoor camera routes',()=>{
 const manifest=JSON.parse(readFileSync(new URL('./blackboard-bundles.json',import.meta.url)));const inputs=manifest.outputs.flatMap(o=>o.inputs);
 for(const name of ['scene.js','campus.js','ocean-study.js','coast-walks.js','classroom-beach-main.js'])assert(!inputs.some(n=>n===name),name);
 assert(inputs.includes('lecture.js'));assert(inputs.includes('board-work.js'));assert(inputs.includes('board-lift-motion.js'));
 const app=readFileSync(new URL('./blackboard-app.js',import.meta.url),'utf8');assert(app.indexOf('constrainHallCamera(camera,controls.target);scene.updateMatrixWorld')<app.indexOf('renderer.render(scene,camera)'));
});
