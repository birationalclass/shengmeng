const assert=require('node:assert/strict'),fs=require('node:fs'),vm=require('node:vm'),path=require('node:path');
class Media extends EventTarget {
  constructor(){super();this.readyState=0;this.src='';this.failDecode=false;this.loads=0;}
  load(){this.loads++;this.readyState=0;if(this.src)queueMicrotask(()=>{this.readyState=this.failDecode?0:2;this.dispatchEvent(new Event(this.failDecode?'error':'loadeddata'));});}
  removeAttribute(){this.src='';}
  play(){throw new Error('Preloading must never play audio');}
}
const context={window:{},AbortController,Blob,URL,setTimeout,clearTimeout,fetch:null};
vm.runInNewContext(fs.readFileSync(path.join(__dirname,'../opening-audio-preload.js'),'utf8'),context);
const flush=()=>new Promise(resolve=>setImmediate(resolve));
(async()=>{
  let stream,calls=0;
  context.fetch=async()=>{calls++;return new Response(new ReadableStream({start(controller){stream=controller;}}),{headers:{'Content-Length':'4'}});};
  const media=new Media(),preload=context.window.CourseOpeningAudioPreload.create(media,'music.mp3'),progress=[];
  let done=false;const task=preload.prepare(value=>progress.push(value)).then(()=>{done=true;});
  await flush();stream.enqueue(new Uint8Array([1,2]));await flush();
  assert.equal(done,false);assert.equal(media.src,'','partial download is not attached to the player');assert.equal(progress.at(-1),.48);
  const subscriber=[];const duplicate=preload.prepare(value=>subscriber.push(value));
  stream.enqueue(new Uint8Array([3,4]));stream.close();await task;await duplicate;
  assert.equal(media.readyState,2);assert.ok(media.src.startsWith('blob:'));assert.equal(subscriber.at(-1),1);assert.equal(progress.at(-1),1);
  await preload.prepare();assert.equal(calls,1,'replay reuses the complete music');assert.equal(media.loads,1);
  URL.revokeObjectURL(media.src);
  let attempts=0;
  context.fetch=async()=>{attempts++;return attempts===1?new Response('',{status:503}):new Response(new Uint8Array([1,2]));};
  const retryMedia=new Media(),retry=context.window.CourseOpeningAudioPreload.create(retryMedia,'retry.mp3');
  await assert.rejects(retry.prepare(),/download failed/);await retry.prepare();assert.equal(attempts,2);assert.equal(retryMedia.readyState,2);URL.revokeObjectURL(retryMedia.src);
  context.fetch=async()=>new Response(new Uint8Array([1,2]));
  const invalid=new Media();invalid.failDecode=true;
  const decoding=context.window.CourseOpeningAudioPreload.create(invalid,'invalid.mp3');
  await assert.rejects(decoding.prepare(),/could not be prepared/);assert.equal(invalid.src,'','failed blob is released');
  invalid.failDecode=false;await decoding.prepare();assert.equal(invalid.readyState,2);URL.revokeObjectURL(invalid.src);
  console.log('PASS: complete download and playable data required, no autoplay, progress subscribers, cached replay, network and decode retry');
})().catch(error=>{console.error(error);process.exitCode=1;});
