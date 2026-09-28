import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync} from 'node:fs';
import {PLAYLIST,createPlaylistPlayer} from './endless-music.mjs';
class AudioMock extends EventTarget{
 paused=true;src='';volume=1;loads=0;
 getAttribute(name){return name==='src'?this.src:null;}
 load(){this.loads++;}
 play(){this.paused=false;return Promise.resolve();}
 pause(){this.paused=true;this.dispatchEvent(new Event('pause'));}
}
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
