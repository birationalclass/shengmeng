import test from 'node:test';
import assert from 'node:assert/strict';
import {ScreenMode,VIDEO_SITES} from './smart-glass-hub.js';
test('media fades reports out and waits for boards to retract',()=>{
 const s=new ScreenMode();s.action('screen:report');for(let i=0;i<10;i++)s.update(.1,0);assert(s.reportAlpha>.99);
 s.action('screen:media');s.update(.1,0);assert(s.reportAlpha>0&&s.reportAlpha<1);assert.equal(s.mediaAlpha,0);
 for(let i=0;i<15;i++)s.update(.1,1);assert(s.reportAlpha<.005);assert(s.mediaAlpha>.99);
 s.action('screen:power');for(let i=0;i<15;i++)s.update(.1,1);assert(s.mediaAlpha<.005);s.action('screen:report');assert(s.power);assert.equal(s.mode,'report');
});
test('power dims after inactivity and pointer activity restores it',()=>{
 const s=new ScreenMode();for(let i=0;i<60;i++)s.update(.1,1);assert(s.brightness<.23);s.wake();for(let i=0;i<8;i++)s.update(.1,1);assert(s.brightness>.99);
});
test('video links use fixed official HTTPS destinations',()=>{assert.deepEqual(VIDEO_SITES.map(s=>new URL(s.url).hostname),['www.bilibili.com','www.iqiyi.com','v.qq.com']);});
