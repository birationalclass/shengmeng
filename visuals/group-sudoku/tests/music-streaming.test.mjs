import test from 'node:test';
import assert from 'node:assert/strict';
import {createBackgroundMusic,MUSIC_KEY} from '../music.mjs';
class Element extends EventTarget{
 constructor(){super();this.attrs=new Map();this.value='';this.checked=false;this.textContent='';}
 setAttribute(k,v){this.attrs.set(k,String(v));}getAttribute(k){return this.attrs.get(k)||null;}removeAttribute(k){this.attrs.delete(k);}closest(){return null;}
}
class Audio extends Element{
 constructor(){super();this.paused=true;this.currentTime=0;this.error=null;this.hang=false;this.loads=0;this.plays=0;}
 set src(v){this.setAttribute('src',v);}get src(){return this.getAttribute('src')||'';}
 load(){this.loads++;this.currentTime=0;this.error=null;if(this.src)this.dispatchEvent(new Event('loadedmetadata'));}
 play(){this.plays++;this.paused=false;if(this.hang)return new Promise(()=>{});this.dispatchEvent(new Event('playing'));return Promise.resolve();}
 pause(){this.paused=true;}
}
test('native media streams, releases disabled buffers, resumes, and retries stalled startup',async()=>{
 const saved=Object.fromEntries(['document','window','location','setTimeout','clearTimeout','fetch'].map(k=>[k,globalThis[k]]));
 const audio=new Audio(),els=new Map(['musicEnabled','musicVolume','musicVolumeValue','musicStatus','musicTitle','musicToggleLabel','musicVolumeLabel'].map(k=>[k,new Element()]));els.set('backgroundMusic',audio);
 const doc=new EventTarget();doc.hidden=false;doc.getElementById=k=>els.get(k);const timers=new Map();let seq=0;
 Object.assign(globalThis,{document:doc,window:new EventTarget(),location:{search:'?mute=1'},setTimeout:fn=>{timers.set(++seq,fn);return seq;},clearTimeout:id=>timers.delete(id),fetch:()=>{throw Error('Never fetch the whole soundtrack');}});
 const flush=async()=>{await Promise.resolve();await Promise.resolve();await Promise.resolve();};
 try{
  const data=new Map(),storage={getItem:k=>data.get(k),setItem:(k,v)=>data.set(k,v)};createBackgroundMusic({storage,t:zh=>zh});
  assert.equal(audio.preload,'metadata');assert.match(audio.src,/magic-study\.mp3\?stream=offline1$/);assert.equal(audio.plays,0);assert.equal(audio.muted,true);
  doc.dispatchEvent(new Event('pointerdown'));await flush();assert.equal(audio.paused,false);assert.equal(timers.size,0);
  audio.currentTime=73;const toggle=els.get('musicEnabled');toggle.checked=false;toggle.dispatchEvent(new Event('change'));assert.equal(audio.paused,true);assert.equal(audio.src,'');assert.equal(JSON.parse(data.get(MUSIC_KEY)).enabled,false);
  toggle.checked=true;toggle.dispatchEvent(new Event('change'));await flush();assert.equal(audio.currentTime,73);assert.equal(audio.paused,false);
  const slider=els.get('musicVolume');slider.value='0';slider.dispatchEvent(new Event('input'));assert.equal(audio.src,'');
  doc.dispatchEvent(new Event('pointerdown'));assert.equal(audio.src,'');
  slider.value='12';slider.dispatchEvent(new Event('input'));await flush();assert.equal(audio.currentTime,73);
  audio.dispatchEvent(new Event('waiting'));assert.match(els.get('musicStatus').textContent,/缓冲/);assert.equal(timers.size,1);
  [...timers.values()][0]();timers.clear();assert.equal(audio.paused,true);assert.equal(audio.src,'');assert.match(els.get('musicStatus').textContent,/重试/);
  doc.dispatchEvent(new Event('pointerdown'));await flush();assert.equal(audio.paused,false);assert.equal(audio.currentTime,73);
  window.dispatchEvent(new Event('pagehide'));assert.equal(audio.src,'');window.dispatchEvent(new Event('pageshow'));await flush();assert.equal(audio.currentTime,73);
 }finally{for(const [k,v]of Object.entries(saved)){if(v===undefined)delete globalThis[k];else globalThis[k]=v;}}
});
