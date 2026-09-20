import test from 'node:test';
import assert from 'node:assert/strict';
import {musicPreferences} from '../music.mjs';
test('music defaults stay quiet and bad storage never breaks the page',()=>{assert.deepEqual(musicPreferences(),{enabled:true,volume:.12});assert.deepEqual(musicPreferences({getItem(){throw Error()}}),{enabled:true,volume:.12});assert.deepEqual(musicPreferences({getItem:()=>'{broken'}),{enabled:true,volume:.12});});
test('stored mute and volume are preserved and out-of-range values clamped',()=>{const prefs=v=>musicPreferences({getItem:()=>JSON.stringify(v)});assert.deepEqual(prefs({enabled:false,volume:.31}),{enabled:false,volume:.31});assert.equal(prefs({volume:100}).volume,1);assert.equal(prefs({volume:-2}).volume,0);assert.equal(prefs({volume:'loud'}).volume,.12);});
