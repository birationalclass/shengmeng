import {readFileSync} from 'node:fs';
import vm from 'node:vm';
import assert from 'node:assert/strict';
const html=readFileSync(new URL('./index.html',import.meta.url),'utf8');
const script=html.match(/<script id="refugeBootstrap">([\s\S]*?)<\/script>/)[1].replace(/import\('\.\/app\.js[^']*'\)\.catch\(fail\);/,'');
function boot(attempt=0){
 const nodes=new Map(),storage=new Map([['refuge-startup-retry',String(attempt)]]),events={};
 let now=0,interval,timeout,destination;
 const get=id=>{if(!nodes.has(id))nodes.set(id,{hidden:id==='error',dataset:{},style:{},handlers:{},setAttribute(k,v){this[k]=v;},addEventListener(k,fn){this.handlers[k]=fn;}});return nodes.get(id);};
 const context={document:{hidden:false,getElementById:get,addEventListener(k,f){events[k]=f;}},navigator:{onLine:true},location:{href:'https://example.test/?view=pavilion',replace(url){destination=url;}},sessionStorage:{getItem:k=>storage.get(k),setItem:(k,v)=>storage.set(k,v),removeItem:k=>storage.delete(k)},console:{error(){}},Date:{now:()=>now},URL,setTimeout:f=>(timeout=f,1),clearTimeout:()=>timeout=null,setInterval:f=>interval=f,addEventListener:(k,f)=>events[k]=f};
 context.window=context;vm.runInNewContext(script,context);
 return {context,get,storage,events,tick(seconds){for(let i=0;i<seconds*4;i++){now+=250;interval();}},click(id){get(id).handlers.click.call(get(id));},get destination(){return destination;},timeout:()=>timeout?.()};
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
 const b=boot();b.click('enterButton');assert.equal(b.storage.get('refuge-entry-requested'),'1');b.context.refugeBoot.fail(new Error('WebGL'));assert.equal(b.get('errorText').textContent,'图形恢复中');b.click('retrySafe');assert.ok(b.destination.includes('safe=1'));assert.ok(b.destination.includes('view=pavilion'));
}
console.log('Arrival: backoff, offline/hidden/pause, recovery, entry and safe retry passed.');
