import test from 'node:test';
import assert from 'node:assert/strict';
import {resourceScore,percentile,bufferBytes} from './optical-budget.js';
test('score penalizes missed frame budgets and greater submitted workload',()=>{
  const base={fps:60,cpu:1,gpu:3,pixels:950000,triangles:860000,target:60};
  const score=resourceScore(base);
  assert.ok(resourceScore({...base,fps:30})<score);
  assert.ok(resourceScore({...base,gpu:16})<score);
  assert.ok(resourceScore({...base,pixels:1500000,triangles:1600000})<score);
  for(const gpu of [null,0,50]){const s=resourceScore({...base,gpu});assert.ok(Number.isFinite(s)&&s>=0&&s<=100);}
});
test('P95 keeps tail costs and does not mutate the measurements',()=>{
  const values=Array.from({length:100},(_,i)=>100-i);
  assert.equal(percentile(values),95);assert.equal(values[0],100);assert.equal(percentile([]),null);
});
test('shared beach / sea buffers count only once',()=>{
  const array=new Float32Array(30),index=new Uint32Array(6);
  const mesh={geometry:{attributes:{position:{array}},index:{array:index}}};
  assert.equal(bufferBytes({traverse:fn=>[mesh,mesh,{}].forEach(fn)}),144);
});
