const assert=require('node:assert/strict');
const fs=require('node:fs');
const vm=require('node:vm');
const path=require('node:path');
class Node extends EventTarget{
  constructor(){super();this.dataset={};this.checked=false;this.hidden=false;this.textContent='';this.files=[];this.classList={toggle(){}};}
  setAttribute(){}
}
class Audio extends Node{
  constructor(src){super();this.src=src;this.paused=true;this.volume=1;this.currentTime=0;this.duration=16.44;this.muted=false;this.plays=0;}
  async play(){this.plays++;this.paused=false;this.dispatchEvent(new Event('playing'));}
  pause(){this.paused=true;this.dispatchEvent(new Event('pause'));}
}
(async()=>{
  const dialog=new Node(),panel=new Node(),music=new Audio(),toggle=new Node();dialog.open=true;
  const controls=Object.fromEntries(['enabled','loop','file','status','play'].map(k=>['[data-voice-'+k+']',new Node()]));
  controls['[data-settings-reset]']=new Node();
  panel.querySelector=s=>controls[s];dialog.querySelector=()=>null;
  const document=new Node();document.hidden=false;document.baseURI='https://example.test/course/';
  document.getElementById=id=>({courseOpening:dialog,openingSettings:panel,openingMusic:music,openingMusicToggle:toggle}[id]);
  const window=new Node();const store=new Map();let voiceAudio;
  const context=vm.createContext({window,document,URL,Audio:class extends Audio{constructor(src){super(src);voiceAudio=this;}},localStorage:{getItem:k=>store.get(k)??null,setItem:(k,v)=>store.set(k,v)}});
  for(const name of ['opening-audio.js','opening-voice.js'])vm.runInContext(fs.readFileSync(path.join(__dirname,'..',name),'utf8'),context);
  const settle=async()=>{await Promise.resolve();await Promise.resolve();};
  window.CourseOpeningAudio.start();await window.CourseOpeningVoice.unlock();
  assert.equal(music.volume,.72);assert.equal(music.paused,false);
  assert.equal(voiceAudio.paused,true);assert.equal(voiceAudio.muted,false);
  window.CourseOpeningVoice.scene(5,true,1);await settle();
  assert.equal(voiceAudio.paused,false);assert.equal(window.CourseOpeningVoice.holdsScene(),true);
  assert.equal(voiceAudio.volume,.8);assert.equal(music.volume,.72,'dialogue must not lower background music');
  voiceAudio.dispatchEvent(new Event('ended'));assert.equal(window.CourseOpeningVoice.holdsScene(),false);assert.equal(music.volume,.72);
  const voice=window.CourseOpeningVoice,loop=controls['[data-voice-loop]'];
  assert.equal(loop.checked,false,'loop is opt-in');
  const once=voiceAudio.plays;
  for(let cycle=1;cycle<=3;cycle++){voice.scene(6,true,1,cycle);voice.scene(5,true,1,cycle);await settle();}
  assert.equal(voiceAudio.plays,once,'default does not replay on later scene visits');
  voice.scene(5,true,1,4);await settle();assert.equal(voiceAudio.plays,once,'single-scene cycle does not replay by default');
  loop.checked=true;loop.dispatchEvent(new Event('change'));
  assert.equal(store.get('courseOpeningVoiceLoop.v1'),'true','loop preference is saved');
  voice.scene(5,true,1,4);await settle();assert.equal(voiceAudio.plays,once+1);
  voiceAudio.dispatchEvent(new Event('ended'));voice.scene(5,true,1,4);await settle();
  assert.equal(voiceAudio.plays,once+1,'the same cycle never starts a continuous audio loop');
  voice.scene(5,true,1,5);await settle();assert.equal(voiceAudio.plays,once+2,'single figure repeats in the next cycle');
  voiceAudio.dispatchEvent(new Event('ended'));voice.scene(6,true,1,5);voice.scene(5,true,1,6);await settle();
  assert.equal(voiceAudio.plays,once+3,'multiple figures repeat on the next visit');
  voiceAudio.dispatchEvent(new Event('ended'));loop.checked=false;loop.dispatchEvent(new Event('change'));
  voice.scene(6,true,1,6);voice.scene(5,true,1,7);await settle();assert.equal(voiceAudio.plays,once+3,'turning loop off preserves the played marker');
  voice.stop();voice.scene(5,true,1,0);await settle();assert.equal(voiceAudio.plays,once+4,'reopening allows one new automatic playback');
  voiceAudio.dispatchEvent(new Event('ended'));
  controls['[data-voice-play]'].dispatchEvent(new Event('click'));await settle();assert.equal(window.CourseOpeningVoice.holdsScene(),true);
  controls['[data-voice-enabled]'].checked=false;controls['[data-voice-enabled]'].dispatchEvent(new Event('change'));
  assert.equal(voiceAudio.paused,true);assert.equal(window.CourseOpeningVoice.holdsScene(),false);assert.equal(music.volume,.72);
  window.CourseOpeningVoice.scene(6,true,1);assert.equal(voiceAudio.paused,true);
  dialog.dispatchEvent(new Event('close'));assert.equal(voiceAudio.paused,true);assert.equal(music.paused,true);
  loop.checked=true;controls['[data-settings-reset]'].dispatchEvent(new Event('click'));assert.equal(loop.checked,false);assert.equal(store.get('courseOpeningVoiceLoop.v1'),'false');
  const waitingCount=voiceAudio.plays;
  voice.scene(5,true,1,8,false);await settle();assert.equal(voiceAudio.plays,waitingCount,'wait for English narration before beginning the verse');
  voice.scene(5,true,1,8,true);await settle();assert.equal(voiceAudio.plays,waitingCount+1,'deferred dialogue starts once English is visible, without reentering the scene');
  voiceAudio.dispatchEvent(new Event('ended'));loop.checked=true;loop.dispatchEvent(new Event('change'));
  voice.scene(5,true,1,9,false);await settle();assert.equal(voiceAudio.plays,waitingCount+1);
  voice.scene(5,true,1,9,true);await settle();assert.equal(voiceAudio.plays,waitingCount+2,'a looping single figure also waits for English');
  console.log('PASS: original dialogue plays, holds its scene, releases on end/disable, and never ducks background music');
})().catch(error=>{console.error(error);process.exitCode=1;});
