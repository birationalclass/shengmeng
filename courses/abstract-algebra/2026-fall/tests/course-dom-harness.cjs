// Run with Node and jsdom 26 available through NODE_PATH (DOM behavior, not visual QA).
const {JSDOM,ResourceLoader,VirtualConsole}=require('jsdom');
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const repo=path.resolve(__dirname,'../../../..');
const prefix='/courses/abstract-algebra/2026-fall/';
const wait=ms=>new Promise(r=>setTimeout(r,ms));
let requests=[],errors=[];
function file(url){const p=new URL(url).pathname;return repo+p;}
class Loader extends ResourceLoader{
 fetch(url,options){
  requests.push(new URL(url).pathname);
  if(url.endsWith('.woff2'))return null;
  const p=file(url);if(!fs.existsSync(p))return Promise.reject(Error('Missing '+p));
  return Promise.resolve(fs.readFileSync(p));
 }
}
function shims(w){
 w.matchMedia=q=>({matches:false,media:q,addEventListener(){},removeEventListener(){}});
 w.ResizeObserver=class{observe(){}disconnect(){}};
 w.HTMLElement.prototype.scrollTo=function(){};w.HTMLElement.prototype.scrollIntoView=function(){};w.HTMLElement.prototype.scrollBy=function(){};
 w.scrollTo=()=>{};w.document.fonts={ready:Promise.resolve(),load:()=>Promise.resolve(),check:()=>true};
 w.HTMLCanvasElement.prototype.getContext=()=>null;
 w.HTMLDialogElement.prototype.showModal=function(){this.open=true};w.HTMLDialogElement.prototype.close=function(){this.open=false};
 w.fetch=async u=>{const url=new URL(u,w.location.href);requests.push(url.pathname);return {ok:true,json:async()=>JSON.parse(fs.readFileSync(file(url)))};};
}
async function lesson(id){
 requests=[];errors=[];
 const folder=/^1\.[12]$/.test(id)?'lesson-1':'lesson-groups';
 const url='http://course.test'+prefix+folder+'/?embedded=1&section='+id+(id==='1.4'?'#set-group-construction':'');
 const vc=new VirtualConsole();vc.on('jsdomError',e=>{if(e.type!=='css parsing')errors.push(e.message)});vc.on('error',e=>errors.push(String(e)));
 const dom=new JSDOM(fs.readFileSync(repo+prefix+folder+'/index.html','utf8'),{url,runScripts:'dangerously',resources:new Loader(),pretendToBeVisual:true,beforeParse:shims,virtualConsole:vc});
 const w=dom.window;
 for(let i=0;i<100&&!w.document.querySelector('#course-load-cover').hidden;i++)await wait(50);
 assert.equal(w.document.querySelector('#course-load-cover').hidden,true,'loader finish '+id+' '+JSON.stringify(errors));
 assert(w.document.querySelector('.notebook-entry'),'notebook '+id);
 assert.deepEqual(requests.filter(x=>/sections\/.*json/.test(x)),[prefix+folder+'/sections/'+id+'.json']);
 if(id==='1.4'){
  assert.equal(w.document.querySelectorAll('.construction-disclosure[open]').length,0);
  assert.equal(w.document.querySelectorAll('.group-construction .xor-lab').length,0,'lazy animation');
  const detail=w.document.querySelector('[data-check=subsets-associativity]');detail.open=true;await wait(40);
  assert(w.document.querySelector('.xor-lab'));
  for(let phase=0;phase<5;phase++){
   w.document.querySelector(`[data-xor-phase="${phase}"]`).click();
   const panels=[...w.document.querySelectorAll('[data-xor-side]')];
   const active=panels.map(p=>[...p.querySelectorAll('[data-in-result=true]')].map(x=>+x.dataset.region));
   if(phase===1)assert.deepEqual(active,[[1,2],[1,2]]);
   if(phase===3)assert.deepEqual(active,[[1,2,5,6],[2,3,4,5]]);
   if(phase===4)assert.deepEqual(active,[[1,2,4,7],[1,2,4,7]]);
  }
  for(let bits=0;bits<8;bits++){w.document.querySelector(`[data-xor-bits="${bits}"]`).click();assert.match(w.document.querySelector('.xor-verdict').textContent,/mod 2/);}
  detail.open=false;await wait(30);assert.equal(w.document.querySelector('.construction-disclosure[open]'),null);
  w.CourseLanguage.set('en');await wait(30);
  assert.match(w.document.querySelector('.notebook-entry.is-current').textContent,/Assuming the axiom/);
  assert.equal(w.document.querySelectorAll('.construction-disclosure[open]').length,0);
  assert.equal(w.document.querySelectorAll('.katex-error').length,0);
 }
 console.log(id, 'loaded; section requests:',requests.filter(x=>x.endsWith('.json')).length,'errors:',errors);
 assert.deepEqual(errors,[]);
}
module.exports={JSDOM,ResourceLoader,VirtualConsole,fs,path,assert,repo,prefix,wait,file,Loader,shims,lesson};
if(require.main===module)(async()=>{for(const id of ['1.1','1.2','1.4','2.5','3.1'])await lesson(id);process.exit(0)})().catch(e=>{console.error(e);process.exit(1)});
