import test from 'node:test';
import assert from 'node:assert/strict';
import {normalizeDepth,createRelief,updateReliefPositions} from './geometry.js';

test('floating-point normalization preserves sub-8-bit detail and handles degenerate data',()=>{
  const result=normalizeDepth([2,2.0001,3,4]);
  assert(result[1]>0 && result[1]<1/255);
  assert.deepEqual(Array.from(normalizeDepth([7,7,NaN])),[.5,.5,.5]);
  assert.deepEqual(Array.from(normalizeDepth([Infinity,NaN])),[.5,.5]);
});
const depth={width:4,height:4,ai:true,values:Float32Array.from({length:16},(_,i)=>i%4<2?0:1)};
test('default mesh is complete; optional separation cuts discontinuities',()=>{
  const continuous=createRelief(depth,1,80,.45,false,6.1);
  const separated=createRelief(depth,1,80,.45,false,6.1,true);
  assert.equal(continuous.indices.length,80*80*6);
  // Use a pixel-sharp depth map at mesh resolution for the occlusion test.
  const sharp={width:81,height:81,ai:true,values:Float32Array.from({length:81*81},(_,i)=>i%81<40?0:1)};
  const cut=createRelief(sharp,1,80,.45,false,6.1,true);
  assert(cut.indices.length<continuous.indices.length);
  assert(separated.indices.length<=continuous.indices.length);
  for(let i=0;i<continuous.indices.length;i+=3){
    const [a,b,c]=continuous.indices.slice(i,i+3).map(n=>n*3),p=continuous.positions;
    assert((p[b]-p[a])*(p[c+1]-p[a+1])-(p[b+1]-p[a+1])*(p[c]-p[a])>0);
  }
});
test('strength updates reuse buffers, preserve projected photograph, and invert correctly',()=>{
  const mesh=createRelief(depth,1.5,160,.45,false,6.1);
  const positions=mesh.positions,indices=mesh.indices,uvs=mesh.uvs;
  updateReliefPositions(mesh,.9,false,6.1);
  assert.equal(mesh.positions,positions);assert.equal(mesh.indices,indices);assert.equal(mesh.uvs,uvs);
  const z=positions[2];
  for(let i=0;i<mesh.count;i++){
    assert(Math.abs(positions[i*3]*6.1/(6.1-positions[i*3+2])-(uvs[i*2]-.5)*mesh.w)<1e-6);
  }
  updateReliefPositions(mesh,.9,true,6.1);assert(Math.abs(positions[2]+z)<1e-6);
  updateReliefPositions(mesh,0,false,6.1);
  for(let i=2;i<positions.length;i+=3)assert.equal(Math.abs(positions[i]),0);
});
