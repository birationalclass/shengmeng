import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync} from 'node:fs';
import {PLAYLIST,createPlaylistPlayer} from './endless-music.mjs';
import {watchPageActivity} from './page-activity.mjs';
class AudioMock extends EventTarget{
 paused=true;src='';volume=1;loads=0;
 getAttribute(name){return name==='src'?this.src:null;}
 load(){this.loads++;}
 play(){this.paused=false;return Promise.resolve();}
 pause(){this.paused=true;this.dispatchEvent(new Event('pause'));}
}
test('blur pauses music without losing preferences and only resumes prior playback',async()=>{
 const audio=new AudioMock(),storage={getItem:()=>null,setItem:()=>{}};
 const player=createPlaylistPlayer({audio,storage});await player.play();
 player.setSuspended(true);assert.equal(audio.paused,true);
 await player.play();assert.equal(audio.paused,true);
 player.setSuspended(false);await Promise.resolve();assert.equal(audio.paused,false);
 player.setEnabled(false);player.setSuspended(true);player.setSuspended(false);assert.equal(audio.paused,true);
});
test('window blur pauses even when document remains visible',()=>{
 const host=new EventTarget(),doc=new EventTarget();let focused=true;doc.hidden=false;doc.hasFocus=()=>focused;host.document=doc;
 const states=[],dispose=watchPageActivity(v=>states.push(v),host);
 focused=false;host.dispatchEvent(new Event('blur'));assert.equal(states.at(-1),false);
 focused=true;host.dispatchEvent(new Event('focus'));assert.equal(states.at(-1),true);
 doc.hidden=true;doc.dispatchEvent(new Event('visibilitychange'));assert.equal(states.at(-1),false);
 dispose();
});
test('Interstellar soundtrack uses the supplied local MP3',()=>{
 assert.equal(PLAYLIST.length,1);assert.equal(PLAYLIST[0].title,'INTERSTELLAR');
 for(const track of PLAYLIST)assert.ok(existsSync(new URL(track.src)));
});
test('end advances once, final track loops, pause and volume persist',async()=>{
 const audio=new AudioMock(),data=new Map();const storage={getItem:k=>data.get(k),setItem:(k,v)=>data.set(k,v)};let state;
 const player=createPlaylistPlayer({audio,storage,onState:s=>state=s});await player.play();
 audio.dispatchEvent(new Event('ended'));await Promise.resolve();assert.equal(state.index,0);
 player.next(-2);await Promise.resolve();assert.equal(state.index,0);
 audio.dispatchEvent(new Event('ended'));await Promise.resolve();assert.equal(state.index,0);assert.equal(audio.loop,false);
 player.setEnabled(false);player.next();assert.equal(audio.paused,true);player.setVolume(.27);
 const restored=new AudioMock();createPlaylistPlayer({audio:restored,storage,onState:s=>state=s});assert.equal(state.enabled,false);assert.equal(state.volume,.27);assert.equal(state.index,0);
});
