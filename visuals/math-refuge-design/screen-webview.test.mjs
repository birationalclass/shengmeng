import test from 'node:test';import assert from 'node:assert/strict';import {screenTransform,screenAddress} from './screen-webview.js';
test('browser surface maps exactly to the perspective glass corners',()=>{
 for(const q of [[[10,20],[510,20],[510,220],[10,220]],[[20,40],[620,10],[590,370],[70,300]]]){
 const m=screenTransform(q,1440,347);[[0,0],[1440,0],[1440,347],[0,347]].forEach(([x,y],i)=>{const w=m[3]*x+m[7]*y+1;assert(Math.abs((m[0]*x+m[4]*y+m[12])/w-q[i][0])<1e-7);assert(Math.abs((m[1]*x+m[5]*y+m[13])/w-q[i][1])<1e-7);});
 }
 assert.equal(screenTransform([[0,0],[0,0],[0,0],[0,0]],1440,347),null);
});

test('address bar accepts ordinary web URLs and rejects embedded credentials',()=>{
 assert.equal(screenAddress('www.bilibili.com'),'https://www.bilibili.com/');assert.throws(()=>screenAddress('https://user:pass@example.org'));
});

test('reject projective poles and invalid corners before sending a CSS matrix',()=>{
 assert.equal(screenTransform([[0,0],[1,0],[0,1],[1,1]],1440,592),null);
 assert.equal(screenTransform([[0,0],[Infinity,0],[1,1],[0,1]],1440,592),null);
});
