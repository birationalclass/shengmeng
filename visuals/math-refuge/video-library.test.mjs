import test from 'node:test';import assert from 'node:assert/strict';
import {videoId,screenPlayerURL} from './video-library.js';
test('video links and BV numbers resolve to the supported screen player',()=>{
 for(const value of ['BV1Qrhe6cEaU','https://www.bilibili.com/video/BV1Qrhe6cEaU/?spm=foo']){assert.equal(videoId(value),'BV1Qrhe6cEaU');const u=new URL(screenPlayerURL(value));assert.equal(u.origin,'https://player.bilibili.com');assert.equal(u.searchParams.get('bvid'),'BV1Qrhe6cEaU');}
 for(const value of ['https://evil.example/video/BV1Qrhe6cEaU/','javascript:alert(1)','BV../../admin'])assert.equal(screenPlayerURL(value),null);
});
