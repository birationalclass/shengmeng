const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const vm=require('node:vm');
const source=fs.readFileSync(path.join(__dirname,'../opening-fonts.js'),'utf8');
function setup(){
  const created=[],loaded=new Set(),timers=new Map();let timerId=0;
  class FontFace{
    constructor(family,src,descriptors){this.family=family;this.src=src;this.descriptors=descriptors;this.status='unloaded';created.push(this);}
    load(){
      if(this.status==='loaded')return Promise.resolve(this);
      if(!this.promise){this.status='loading';this.promise=new Promise((resolve,reject)=>{
        this.resolve=()=>{this.status='loaded';resolve(this);};
        this.reject=()=>{this.status='error';reject(new Error('Font request failed'));};
      });}
      return this.promise;
    }
  }
  const context={URL,FontFace,window:{},document:{currentScript:{src:'https://example.test/courses/abstract-algebra/2026-fall/opening-fonts.js'},fonts:loaded},setTimeout(fn){timers.set(++timerId,fn);return timerId;},clearTimeout(id){timers.delete(id);}};
  vm.runInNewContext(source,context);
  return {api:context.window.CourseOpeningFonts,created,loaded,timers};
}
const flush=async()=>{for(let i=0;i<8;i++)await Promise.resolve();};
(async()=>{
  const first=setup(),progress=[];let ready=false;
  const a=first.api.prepare(value=>progress.push(value));a.then(()=>{ready=true;});
  assert.equal(first.created.length,6);
  assert.equal(a,first.api.prepare(),'concurrent initialization shares font work');
  first.created.slice(0,-1).forEach(face=>face.resolve());await flush();
  assert.equal(ready,false,'no geometry is ready while one required font remains pending');
  first.created.at(-1).resolve();await a;
  assert.equal(first.loaded.size,6);assert.equal(progress.at(-1),1);assert.equal(first.timers.size,0);
  await first.api.prepare();assert.equal(first.created.length,6,'replay reuses decoded fonts');

  const failure=setup(),bad=failure.api.prepare(),caught=assert.rejects(bad,error=>error.fontLoading===true);
  failure.created.slice(1).forEach(face=>face.resolve());failure.created[0].reject();await caught;
  const retry=failure.api.prepare();assert.equal(failure.created.length,7,'retry retains completed fonts and replaces a failed face');
  assert.match(failure.created.at(-1).src,/font-retry=2/);
  failure.created.at(-1).resolve();await retry;
  assert.equal(failure.loaded.size,6);assert.equal(failure.timers.size,0);

  const slow=setup(),timeout=slow.api.prepare(),timedOut=assert.rejects(timeout,error=>error.fontLoading===true&&/timed out/.test(error.message));
  [...slow.timers.values()][0]();await timedOut;
  const afterTimeout=slow.api.prepare();
  assert.equal(slow.created.length,12,'timed-out requests do not trap a later retry');
  slow.created.slice(6).forEach(face=>face.resolve());await afterTimeout;
  console.log('PASS opening fonts: full readiness barrier, shared loading, failed-font retry and timeout recovery');
})().catch(error=>{console.error(error);process.exitCode=1;});
