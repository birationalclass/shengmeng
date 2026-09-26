import test from 'node:test';
import assert from 'node:assert/strict';
import * as THREE from '../3d/vendor/three.module.js';
import {EllipticRenderer} from './elliptic-renderer.js';

test('distant sea fills sky pixels without writing depth or covering foreground objects',()=>{
 const renderer={domElement:{dataset:{}}};
 const ocean=new EllipticRenderer(null,new THREE.Texture(),{renderer,sky:false,backgroundOrder:1001});
 const background=ocean.farOcean;
 assert.equal(background.renderOrder,1001);assert(!background.material.transparent);
 assert(background.material.depthTest);assert.equal(background.material.depthFunc,THREE.LessEqualDepth);
 assert(!background.material.depthWrite);
 assert.match(background.material.vertexShader,/gl_Position=vec4\(position.xy,1\.,1\.\)/);
 assert.doesNotMatch(background.material.fragmentShader,/gl_FragDepth|uProjection|<9000/);
 // Its far-depth fragment passes the untouched sky depth but fails wherever
 // a real object has already written depth. It cannot occlude later waves.
 for(const objectDepth of [.01,.5,.99,.99999])assert(!(1<=objectDepth));
 assert(1<=1);
 for(const height of [2,20,450,1800]){
  ocean.camera.position.set(-1000,height,0);ocean.camera.lookAt(2000,0,0);
  ocean.draw({time:7,tide:2.55,tidal:false,wave:.6,sun:-1,view:'aerial'},{render:false});
  for(const x of [-1,0,1])for(const y of [-1,0,1]){
   const ray=new THREE.Vector4(x,y,1,1).applyMatrix4(ocean.uniforms.uInverseProjection.value);
   const direction=new THREE.Vector3(ray.x,ray.y,ray.z).transformDirection(ocean.uniforms.uCameraWorld.value);
   const expected=new THREE.Vector3(x,y,1).unproject(ocean.camera).sub(ocean.camera.position).normalize();
   assert(direction.distanceTo(expected)<1e-8,'Background rays track the elevated opening camera');
  }
 }
 const geometries=new Set(),materials=new Set();ocean.scene.traverse(o=>{if(o.geometry)geometries.add(o.geometry);if(o.material)materials.add(o.material);});
 geometries.forEach(g=>g.dispose());materials.add(ocean.waterFar);materials.forEach(m=>m.dispose());
});
