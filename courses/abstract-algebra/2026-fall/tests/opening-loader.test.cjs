const assert=require('node:assert/strict'),fs=require('node:fs'),vm=require('node:vm'),path=require('node:path');
const html=fs.readFileSync(path.join(__dirname,'../index.html'),'utf8');
const script=[...html.matchAll(/<script>([\s\S]*?)<\/script>/g)].map(m=>m[1]).find(s=>s.includes('CourseOpeningBoot'));
class Node{
 constructor(){this.open=false;this.hidden=false;this.children=new Map();this.attrs={};const s=new Set();this.classList={add:(...v)=>v.forEach(x=>s.add(x)),remove:(...v)=>v.forEach(x=>s.delete(x)),contains:x=>s.has(x)};}
 querySelector(s){if(!this.children.has(s))this.children.set(s,new Node());return this.children.get(s);}
 getContext(){return null;}addEventListener(){}focus(){}showModal(){this.open=true;}close(){this.open=false;}setAttribute(k,v){this.attrs[k]=v;}
}
const nodes=new Map(),document={body:new Node(),documentElement:new Node(),addEventListener(){},getElementById(id){if(!nodes.has(id))nodes.set(id,new Node());return nodes.get(id);}};
const timers=new Map();let timer=0;
const ctx={window:{},document,location:{hash:''},matchMedia:()=>({matches:false}),requestAnimationFrame:()=>1,cancelAnimationFrame(){},setTimeout:fn=>{timers.set(++timer,fn);return timer;},clearTimeout:id=>timers.delete(id)};
vm.runInNewContext(script,ctx);
const boot=ctx.window.CourseOpeningBoot,dialog=nodes.get('courseOpening'),loader=nodes.get('openingLoader'),start=loader.querySelector('[data-start-animation]');
assert.equal(loader.hidden,false);assert.equal(start.hidden,true);assert.equal(dialog.open,true);assert.equal(timers.size,1);
boot.advance(55,'加载');boot.ready();assert.equal(start.hidden,false);assert.equal(timers.size,0);
boot.finish();assert.equal(loader.hidden,true);assert.equal(start.hidden,true);
boot.ready();boot.advance(70,'迟到的加载事件');assert.equal(loader.hidden,true);assert.equal(start.hidden,true);assert.equal(boot.progress,100);
boot.stop();dialog.close();boot.ready();assert.equal(loader.hidden,true);
boot.start();assert.equal(loader.hidden,false);assert.equal(start.hidden,true);assert.equal(boot.progress,0);assert.equal(dialog.classList.contains('opening-ready'),false);
boot.start();assert.equal(timers.size,1,'a replay has only one loading watchdog');
boot.ready();boot.finish();assert.equal(loader.hidden,true);
boot.start();boot.dismiss();assert.equal(dialog.open,false);assert.equal(loader.hidden,true);assert.equal(timers.size,0);
boot.ready();assert.equal(start.hidden,true);
console.log('PASS: loader is removed before playback, ignores late readiness, and resets cleanly for replay');
