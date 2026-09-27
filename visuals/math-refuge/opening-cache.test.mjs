import test from 'node:test';import assert from 'node:assert/strict';
import {OpeningCache} from './opening-cache.js';
function fixture(options={}){
 const surfaces=[],states=[],renders=[],draws=[];let restored=0;
 class Frame{constructor(source,{timestamp=0}={}){this.timestamp=timestamp;this.closed=false;surfaces.push(this);}close(){this.closed=true;}}
 class Encoder{
  static async isConfigSupported(config){return {supported:true,config};}
  constructor(callbacks){this.callbacks=callbacks;this.encodeQueueSize=0;this.state='unconfigured';}
  configure(c){this.config=c;this.state='configured';}
  encode(f){this.callbacks.output({timestamp:f.timestamp,byteLength:options.chunkBytes||100,type:'key'},{decoderConfig:{codec:this.config.codec}});}
  async flush(){}close(){this.state='closed';}
 }
 class Decoder{
  static async isConfigSupported(){return {supported:true};}
  constructor(callbacks){this.callbacks=callbacks;this.state='unconfigured';}
  configure(){this.state='configured';}decode(c){this.callbacks.output(new Frame(null,{timestamp:c.timestamp}));}close(){this.state='closed';}
 }
 const cache=new OpeningCache({canvas:{width:1280,height:720},api:{VideoEncoder:Encoder,VideoDecoder:Decoder,VideoFrame:Frame},seconds:.25,onState:s=>states.push(s),onRestore:()=>restored++,...options});
 return {cache,surfaces,states,renders,draws,render:t=>renders.push(t),context:{drawImage(f){assert(!f.closed);draws.push(f.timestamp);}},restores:()=>restored};
}
test('completed frames play without invoking 3D rendering; decoded memory is bounded and released',async()=>{
 const f=fixture();await f.cache.start();while(f.cache.state==='recording')f.cache.capture(f.render);await Promise.resolve();await Promise.resolve();
 assert.equal(f.cache.state,'ready');assert.equal(f.renders.length,16);assert.equal(f.restores(),1);assert(f.cache.frames.size<=4);
 assert(f.cache.play());const renderCount=f.renders.length;
 for(let i=0;i<20&&f.cache.state==='playing';i++){f.cache.present(1/60,f.context);assert(f.surfaces.filter(x=>!x.closed).length<=4);}
 assert.equal(f.cache.state,'finished');assert.equal(f.renders.length,renderCount);assert(f.draws.length>=14);assert(f.surfaces.every(x=>x.closed));assert.equal(f.cache.bytes,0);
});
test('entering during capture immediately releases the partial cache and cannot play it',async()=>{
 const f=fixture();await f.cache.start();f.cache.capture(f.render);f.cache.abort();assert.equal(f.cache.state,'cancelled');assert.equal(f.restores(),1);assert.equal(f.cache.play(),false);assert(f.surfaces.every(x=>x.closed));
});
test('a click during asynchronous capability detection cannot later begin recording',async()=>{
 const f=fixture();const preparing=f.cache.start();f.cache.abort();await preparing;assert.equal(f.cache.state,'cancelled');assert.equal(f.cache.encoder,null);
});
test('a large display or missing codec falls back without resizing or blocking the canvas',async()=>{
 for(const options of [{canvas:{width:7680,height:4320}},{api:{}}]){const f=fixture(options);await f.cache.start();assert.equal(f.cache.state,'unavailable');assert.equal(f.cache.play(),false);assert.equal(f.cache.canvas.width,options.canvas?.width||1280);}
});
test('compressed cache has a hard memory bound',async()=>{
 const f=fixture({chunkBytes:33*1024*1024});await f.cache.start();f.cache.capture(f.render);assert.equal(f.cache.state,'memory-limit');assert.equal(f.cache.bytes,0);assert(f.surfaces.every(x=>x.closed));
});
test('entry during encoder flush never resurrects a decoder or ready cache',async()=>{
 const f=fixture();await f.cache.start();while(f.cache.state==='recording')f.cache.capture(f.render);assert.equal(f.cache.state,'flushing');f.cache.abort();await Promise.resolve();await Promise.resolve();assert.equal(f.cache.state,'cancelled');assert.equal(f.cache.decoder,null);assert(f.surfaces.every(x=>x.closed));
});
