import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {normalizeDepth} from './geometry.js';

const code=(await readFile(new URL('./depth-worker.js',import.meta.url),'utf8'))
  .replace(/^import .*;$/m,'')
  .replace("await import('./vendor/transformers.min.js')",'await getEngine()');
function worker(engine,gpu) {
  const messages=[],self={postMessage:message=>messages.push(message)};
  new Function('self','navigator','getEngine','normalizeDepth',code)(self,{gpu},async()=>engine,normalizeDepth);
  return {self,messages};
}
const output={depth:{width:2,height:2},predicted_depth:{data:new Float32Array([1,1.0001,2,3])}};
const env=()=>({backends:{onnx:{wasm:{}}}});
test('worker uses raw tensor dimensions and retains floating-point depth',async()=>{
  const {self,messages}=worker({env:env(),pipeline:async()=>async()=>output});
  await self.onmessage({data:{id:7,image:'local-image'}});
  const result=messages.find(m=>m.type==='result');
  assert.equal(result.id,7);assert.equal(result.backend,'WASM');
  assert.equal(result.width*result.height,result.values.length);
  assert(result.values[1]>0 && result.values[1]<1/255);
});
test('GPU inference failure retries WASM and reports invalid dimensions as an error',async()=>{
  const devices=[];
  const {self,messages}=worker({env:env(),pipeline:async(_task,_model,options)=>{
    devices.push(options.device);
    if(options.device==='wasm')return async()=>output;
    const estimator=async()=>{throw new Error('GPU failure');};estimator.dispose=async()=>{};return estimator;
  }},{requestAdapter:async()=>({})});
  await self.onmessage({data:{id:1,image:'local-image'}});
  assert.deepEqual(devices,['webgpu','wasm']);assert.equal(messages.at(-1).backend,'WASM');
  const invalid=worker({env:env(),pipeline:async()=>async()=>({...output,depth:{width:3,height:3}})});
  await invalid.self.onmessage({data:{id:2,image:'local-image'}});
  assert.equal(invalid.messages.at(-1).type,'error');
});
