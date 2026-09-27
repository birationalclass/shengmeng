import {readFileSync} from 'node:fs';
import vm from 'node:vm';
import assert from 'node:assert/strict';
const html=readFileSync(new URL('./index.html',import.meta.url),'utf8');
const script=html.match(/<script id="refugeBootstrap">([\s\S]*?)<\/script>/)[1].replace(/import\('\.\/app\.js[^']*'\)\.catch\(fail\);/,'');
function boot(attempt=0,viewport){
 const nodes=new Map(),storage=new Map([['refuge-startup-retry',String(attempt)]]),events={};
 let now=0,interval,destination,nextTimer=0;const timers=new Map();
 const classes=()=>{const values=new Set(['arriving','awaiting-scene']);return {add(...items){items.forEach(x=>values.add(x));},remove(...items){items.forEach(x=>values.delete(x));},toggle(x,on){if(on)values.add(x);else values.delete(x);},contains:x=>values.has(x)};};
 const get=id=>{if(!nodes.has(id))nodes.set(id,{hidden:id==='error',classList:classes(),dataset:{},style:{setProperty(k,v){this[k]=v;}},handlers:{},getAttribute(k){return this[k]??(id==='loadFill'&&k==='d'?html.match(/id="loadFill"[^>]* d="([^"]+)"/)[1]:null);},setAttribute(k,v){this[k]=v;},addEventListener(k,fn){this.handlers[k]=fn;}});return nodes.get(id);};
 const context={innerWidth:viewport?.width,innerHeight:viewport?.height,Event:class {constructor(type){this.type=type;}},dispatchEvent:e=>events[e.type]?.(e),document:{hidden:false,hasFocus:()=>true,querySelector:()=>null,body:{classList:classes()},getElementById:get,addEventListener(k,f){events[k]=f;}},navigator:{onLine:true},location:{href:'https://example.test/?view=pavilion',replace(url){destination=url;}},sessionStorage:{getItem:k=>storage.get(k),setItem:(k,v)=>storage.set(k,v),removeItem:k=>storage.delete(k)},console:{error(){}},Date:{now:()=>now},URL,setTimeout:(f,ms)=>{const id=++nextTimer;timers.set(id,{f,at:now+ms});return id;},clearTimeout:id=>timers.delete(id),setInterval:f=>interval=f,addEventListener:(k,f)=>events[k]=f};
 context.window=context;vm.runInNewContext(script,context);
 return {context,get,storage,events,tick(seconds){for(let i=0;i<seconds*4;i++){now+=250;interval();for(const [id,timer] of timers)if(timer.at<=now){timers.delete(id);timer.f();}}},click(id){get(id).handlers.click.call(get(id));},get destination(){return destination;},timeout:()=>timers.get(context.refugeLoadingTimer)?.f()};
}
for(const [attempt,delay] of [[0,8],[1,15],[2,30],[3,60],[8,60]]){
 const b=boot(attempt);b.context.refugeBoot.fail(new Error('network'));b.tick(delay-1);assert.equal(b.destination,undefined);b.tick(1);assert.ok(b.destination.includes('_retry='));assert.equal(b.storage.get('refuge-startup-retry'),String(attempt+1));
}
{
 const b=boot();b.context.refugeBoot.fail(new Error('network'));b.context.navigator.onLine=false;b.tick(30);assert.equal(b.destination,undefined);assert.equal(b.get('retryStatus').textContent,'等待网络');b.context.navigator.onLine=true;b.context.document.hidden=true;b.tick(20);assert.equal(b.destination,undefined);b.context.document.hidden=false;b.click('retryPause');b.tick(20);assert.equal(b.destination,undefined);b.click('retryPause');b.events.online();b.tick(1);assert.ok(b.destination);
}
{
 const b=boot();b.timeout();assert.equal(b.get('error').hidden,false);b.context.refugeBoot.ready();b.tick(60);assert.equal(b.destination,undefined);assert.equal(b.get('error').hidden,true);assert.equal(b.get('loading').hidden,false);assert.equal(b.get('loadProgress')['aria-valuenow'],'100');b.context.refugeBoot.entered();assert.equal(b.get('loading').hidden,true);
}
{
 const b=boot();b.context.refugeBoot.auth('authenticated');b.click('enterButton');assert.equal(b.storage.get('refuge-entry-requested'),'1');b.context.refugeBoot.fail(new Error('WebGL'));assert.equal(b.get('errorText').textContent,'图形恢复中');b.click('retrySafe');assert.ok(b.destination.includes('safe=1'));assert.ok(b.destination.includes('view=pavilion'));
}
console.log('Arrival: backoff, offline/hidden/pause, recovery, entry and safe retry passed.');

{
 const b=boot();let requests=0,logins=0;b.events['refuge-entry']=()=>requests++;b.events['refuge-login']=()=>logins++;
 b.context.refugeBoot.ready();b.click('enterButton');assert.equal(requests,0,'pending auth must not enter');
 b.context.refugeBoot.auth('anonymous');b.click('enterButton');assert.equal(logins,1);assert.equal(requests,0);
 b.context.refugeBoot.auth('authenticated');assert.equal(requests,0,'auto login waits for a click');assert.equal(b.get('enterButton').textContent,'点击继续');
 b.click('enterButton');assert.equal(requests,1);assert.equal(b.get('loading').dataset.entryRequested,'true');
 b.context.refugeBoot.entered();b.context.refugeBoot.requestEntry();assert.equal(requests,1,'entry cannot run twice');
}
{
 const b=boot();b.context.refugeBoot.auth('authenticated');b.context.refugeBoot.requestEntry();assert.equal(b.get('entryStatus').textContent,'正在准备开场');b.context.refugeBoot.ready();assert.equal(b.get('enterButton').hidden,true,'login during loading keeps the entry queued');
}

{
 const b=boot();let reveals=0;b.events['refuge-preview-ready']=()=>reveals++;
 b.context.refugeBoot.auth('anonymous');b.context.refugeBoot.ready();
 assert(b.context.document.body.classList.contains('awaiting-scene'),'assets/session readiness cannot expose a blank canvas');
 assert.equal(b.context.refugeBoot.previewReady,false);
 b.context.refugeBoot.preview();assert(b.context.document.body.classList.contains('awaiting-scene'),'entry waits while the live reveal expands');assert.equal(reveals,0);
 b.tick(1);assert.equal(reveals,0,'login waits until the real-frame fade completes');
 b.tick(.5);assert.equal(reveals,1);assert.equal(b.context.refugeBoot.previewReady,true);
 b.context.refugeBoot.preview();b.tick(2);assert.equal(reveals,1,'later frames must not restart the fade');
}
assert(!html.includes('id="arrivalSea"'),'no static poster replaces the live canvas');

for(const type of ['click','keydown']){
 const b=boot();let entries=0;const e={type,key:'a',target:{closest:()=>null},preventDefault(){this.prevented=true;},stopImmediatePropagation(){this.stopped=true;}};
 b.events['refuge-entry']=()=>entries++;b.context.refugeBoot.auth('authenticated');b.context.refugeBoot.ready();
 b.events[type](e);assert.equal(entries,0,'A blank/unrevealed startup cannot accidentally enter');
 b.context.refugeBoot.preview();b.tick(2);b.events[type](e);
 assert.equal(entries,1);assert(e.prevented&&e.stopped,'The entry gesture cannot also move the newly entered camera');
 b.events[type](e);assert.equal(entries,1,'One entry per visit even with double clicks');
}
for(const blocker of ['dialog','input','shortcut','composition']){
 const b=boot();let entries=0;b.events['refuge-entry']=()=>entries++;b.context.refugeBoot.auth('authenticated');b.context.refugeBoot.ready();b.context.refugeBoot.preview();b.tick(2);
 b.context.document.querySelector=()=>blocker==='dialog'?{}:null;
 const event={type:'keydown',key:'a',ctrlKey:blocker==='shortcut',isComposing:blocker==='composition',target:{closest:()=>blocker==='input'?{}:null},preventDefault(){},stopImmediatePropagation(){}};
 b.events.keydown(event);assert.equal(entries,0,blocker+' cannot trigger scene entry');
}
{
 const b=boot();let logins=0,entries=0;b.events['refuge-login']=()=>logins++;b.events['refuge-entry']=()=>entries++;
 b.context.refugeBoot.auth('anonymous');b.context.refugeBoot.ready();b.context.refugeBoot.preview();b.tick(2);
 b.events.click({type:'click',target:{closest:()=>null},preventDefault(){},stopImmediatePropagation(){}});
 assert.equal(logins,1);assert.equal(entries,0,'A background gesture never bypasses login');
}

for(const type of ['click','keydown']){
 const b=boot();b.context.refugeBoot.auth('anonymous');b.context.refugeBoot.preview();b.tick(2);b.context.document.querySelector=()=>({open:true});
 b.events[type]({type,key:'a',target:{closest:()=>null},preventDefault(){assert.fail('modal input must retain native behavior');},stopImmediatePropagation(){assert.fail('modal input must not be captured by entry');}});
}

{
 const b=boot();b.context.refugeBoot.stage(45,'海岸');b.context.refugeBoot.stage(20,'旧回调');
 assert.equal(b.get('loadProgress')['aria-valuenow'],'45','out-of-order callbacks cannot reverse progress');

 b.context.refugeBoot.preview();assert(b.context.document.body.classList.contains('awaiting-scene'),'partial real frames do not unlock entry');
 b.context.refugeBoot.stage(NaN,'invalid');assert.equal(b.get('loadProgress')['aria-valuenow'],'45');
}

{
 const b=boot();b.context.refugeBoot.stage(66,'');
 assert.equal(b.get('arrivalVeil').style['--arrival-radius'],'0%','never reveal an unrendered canvas');
 b.context.refugeBoot.preview();assert.equal(b.get('arrivalVeil').style['--arrival-radius'],'18%');
 assert(b.context.document.body.classList.contains('live-preview'));
 b.context.refugeBoot.stage(80,'');assert.equal(b.get('arrivalVeil').style['--arrival-radius'],'60%');
 b.context.refugeBoot.stage(70,'');assert.equal(b.get('arrivalVeil').style['--arrival-radius'],'60%','late callbacks cannot shrink the reveal');
 b.context.refugeBoot.ready();b.context.refugeBoot.preview();
 assert.equal(b.get('arrivalVeil').style['--arrival-radius'],'120%');
 assert.equal(b.context.refugeBoot.previewReady,false);b.tick(1.5);
 assert.equal(b.context.refugeBoot.previewReady,true);
 assert.equal(b.get('arrivalVeil').hidden,true,'completed reveal removes the covering layer');
 assert(!b.context.document.body.classList.contains('awaiting-scene'));
 await b.context.refugeBoot.exitCoast();
 assert(b.context.document.body.classList.contains('live-preview'),'entry preserves the visible live scene');
}

for(const auth of ['pending','anonymous']){
 const b=boot();b.context.refugeBoot.auth(auth);b.context.document.querySelector=()=>({open:true});
 let resumed=false;const work=b.context.refugeBoot.waitForEntryUI().then(()=>resumed=true);
 b.tick(.25);await work;
 assert(resumed,'an open login dialog and pending auth cannot block scene construction');
 assert.equal(b.context.refugeBoot.authorized,false,'background loading cannot bypass authentication');
}

const app=readFileSync(new URL('./app.js',import.meta.url),'utf8');
assert(!app.includes('ready();window.refugeBoot?.preview()'),'readiness alone cannot certify a rendered frame');
