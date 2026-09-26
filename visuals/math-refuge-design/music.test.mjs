import test from 'node:test';
import assert from 'node:assert/strict';
import {createBackgroundMusic} from './background-music.js';

function fixture(saved={}){
  class Element extends EventTarget{
    constructor(){super();this.attributes={};this.dataset={};}
    setAttribute(k,v){this.attributes[k]=v;}getAttribute(k){return this.attributes[k]??null;}
  }
  const audio=new Element(),button=new Element(),volume=new Element(),readout={},events=new Element(),frames=new Map(),data=new Map(Object.entries(saved));
  let time=0,id=0;audio.paused=true;audio.dataset.src='./assets/audio/norway-ambient.m4a';audio.attempts=0;
  Object.defineProperty(audio,'src',{set(v){this.setAttribute('src',v);}});
  audio.play=async()=>{audio.attempts++;if(audio.blocked)throw Object.assign(new Error('blocked'),{name:'NotAllowedError'});audio.paused=false;};
  audio.pause=()=>{audio.paused=true;};
  const player=createBackgroundMusic({audio,button,volume,readout,events,storage:{getItem:k=>data.get(k)??null,setItem:(k,v)=>data.set(k,v)},
    now:()=>time,requestFrame:fn=>{frames.set(++id,fn);return id;},cancelFrame:n=>frames.delete(n)});
  return {audio,button,volume,readout,events,data,player,advance(){time+=1000;const pending=[...frames.values()];frames.clear();pending.forEach(fn=>fn());}};
}
test('background music loads on demand, fades, remembers controls and follows tab visibility',async()=>{
  const f=fixture();assert.equal(f.audio.attempts,0);assert.equal(f.audio.getAttribute('src'),null);assert.equal(f.volume.value,'18');assert(f.audio.loop);
  f.events.dispatchEvent(new Event('pointerdown'));assert.equal(f.audio.attempts,0,'Other page interactions do not bypass the entrance');
  await f.player.start();f.advance();assert.equal(f.audio.volume,.18);assert(!f.audio.paused);assert.equal(f.button.getAttribute('aria-pressed'),'true');
  f.volume.value='37';f.volume.dispatchEvent(new Event('input'));f.advance();assert.equal(f.audio.volume,.37);assert.equal(f.readout.textContent,'37%');
  f.events.hidden=true;f.events.dispatchEvent(new Event('visibilitychange'));assert(f.audio.paused);
  f.events.hidden=false;f.events.dispatchEvent(new Event('visibilitychange'));await Promise.resolve();f.advance();assert(!f.audio.paused);
  f.button.dispatchEvent(new Event('click'));f.volume.value='12';f.volume.dispatchEvent(new Event('input'));f.advance();assert(f.audio.paused,'Volume adjustment must not cancel a pending pause');
  assert.equal(f.data.get('refuge-music-enabled'),'false');
  f.events.hidden=true;f.events.dispatchEvent(new Event('visibilitychange'));f.events.hidden=false;f.events.dispatchEvent(new Event('visibilitychange'));assert(f.audio.paused,'Explicit pause survives returning to the tab');
  f.player.dispose();
});
test('blocked playback stays retryable and fast pause cannot restart the music',async()=>{
  const f=fixture({'refuge-music-volume':'0','refuge-music-enabled':'false'});assert.equal(f.volume.value,'0');
  f.audio.blocked=true;f.button.dispatchEvent(new Event('click'));await Promise.resolve();assert.equal(f.button.getAttribute('aria-pressed'),'false');assert.equal(f.button.getAttribute('aria-label'),'播放背景音乐');
  f.audio.blocked=false;f.button.dispatchEvent(new Event('click'));f.button.dispatchEvent(new Event('click'));await Promise.resolve();f.advance();assert(f.audio.paused);
  f.button.dispatchEvent(new Event('click'));await Promise.resolve();f.advance();assert(!f.audio.paused);assert.equal(f.audio.volume,0,'Remember a deliberately muted volume');f.player.dispose();assert(f.audio.paused);
});
