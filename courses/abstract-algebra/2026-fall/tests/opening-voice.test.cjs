const assert=require('node:assert/strict');
const fs=require('node:fs');
const vm=require('node:vm');
const path=require('node:path');
class Node extends EventTarget{
  constructor(){super();this.dataset={};this.checked=false;this.hidden=false;this.textContent='';this.files=[];this.classList={toggle(){}};}
  setAttribute(){}
}
class Audio extends Node{
  constructor(src){super();this.src=src;this.paused=true;this.volume=1;this.currentTime=0;this.duration=16.44;this.muted=false;}
  async play(){this.paused=false;this.dispatchEvent(new Event('playing'));}
  pause(){this.paused=true;this.dispatchEvent(new Event('pause'));}
}
(async()=>{
  const dialog=new Node(),panel=new Node(),music=new Audio(),toggle=new Node();dialog.open=true;
  const controls=Object.fromEntries(['enabled','file','status','play'].map(k=>['[data-voice-'+k+']',new Node()]));
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
  controls['[data-voice-play]'].dispatchEvent(new Event('click'));await settle();assert.equal(window.CourseOpeningVoice.holdsScene(),true);
  controls['[data-voice-enabled]'].checked=false;controls['[data-voice-enabled]'].dispatchEvent(new Event('change'));
  assert.equal(voiceAudio.paused,true);assert.equal(window.CourseOpeningVoice.holdsScene(),false);assert.equal(music.volume,.72);
  window.CourseOpeningVoice.scene(6,true,1);assert.equal(voiceAudio.paused,true);
  dialog.dispatchEvent(new Event('close'));assert.equal(voiceAudio.paused,true);assert.equal(music.paused,true);
  console.log('PASS: original dialogue plays, holds its scene, releases on end/disable, and never ducks background music');
})().catch(error=>{console.error(error);process.exitCode=1;});
