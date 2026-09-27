// DOM interaction checks. Requires jsdom 26 via NODE_PATH; does not replace visual QA.
import {createRequire} from 'node:module';import * as models from './models.js';import {fileURLToPath} from 'node:url';
const require=createRequire(import.meta.url),{JSDOM,VirtualConsole}=require('jsdom'),fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const here=path.dirname(fileURLToPath(import.meta.url)),repo=path.resolve(here,'../../..'),wait=ms=>new Promise(r=>setTimeout(r,ms));
const data=JSON.parse(fs.readFileSync(path.join(here,'../2026-fall/lesson-groups/sections/1.6.json')));
const source=fs.readFileSync(path.join(here,'app.js'),'utf8').replace(/^import[^\n]+\n/,'const {suits,ranks,name,rank,codes,outShuffle,inShuffle,encodeFive,targetRoute}=window.MagicModels;\n');
const errors=[],vc=new VirtualConsole();vc.on('jsdomError',e=>errors.push(e.message));
const dom=new JSDOM(fs.readFileSync(path.join(here,'index.html'),'utf8'),{url:'https://course.test/courses/abstract-algebra/card-magic/',runScripts:'outside-only',pretendToBeVisual:true,virtualConsole:vc});const w=dom.window,d=w.document;
w.MagicModels=models;w.fetch=async()=>({ok:true,json:async()=>data});w.eval(fs.readFileSync(path.join(repo,'study/spectral/vendor/katex.min.js'),'utf8'));await w.eval('(async()=>{'+source+'})()');
assert.equal(d.querySelectorAll('.hand .playing-card').length,5);assert.equal(d.querySelectorAll('details[open]').length,0);
// Selecting a duplicate must swap, never silently create an invalid hand.
const chooser=d.querySelector('[data-card-slot="0"]');chooser.value='10';chooser.dispatchEvent(new w.Event('change',{bubbles:true}));assert.equal(new Set([...d.querySelectorAll('.card-choice')].map(x=>x.value)).size,5);
for(let step=0;step<3;step++)d.querySelector('[data-next]').click();assert.equal(d.querySelectorAll('.playing-card.back').length,0);assert.match(d.querySelector('.explanation').textContent,/隐藏牌/);
w.location.hash='perfect-shuffle';await wait(20);for(let i=0;i<3;i++)d.querySelector('[data-shuffle]').click();assert.match(d.querySelector('.explanation').textContent,/恢复原序/);assert.equal(d.querySelector('[data-card="1"]').style.getPropertyValue('--slot'),'1');
const size=d.querySelector('#deck-size');size.value='52';size.dispatchEvent(new w.Event('change',{bubbles:true}));for(let i=0;i<8;i++)d.querySelector('[data-shuffle]').click();assert.match(d.querySelector('.explanation').textContent,/恢复原序/);assert.equal(d.querySelectorAll('.deck-grid span').length,52);
w.location.hash='chosen-position';await wait(20);const input=d.querySelector('#target-position');assert.equal(input.inputMode,'numeric');input.value='52';d.querySelector('form').dispatchEvent(new w.Event('submit',{bubbles:true,cancelable:true}));for(let i=0;i<6;i++)d.querySelector('[data-route-next]').click();assert(d.querySelector('.deck-grid span:last-child').classList.contains('tracked'));assert(d.querySelector('[data-route-next]').disabled);
d.querySelector('#language').click();assert.equal(d.documentElement.lang,'en');assert.match(d.querySelector('.lab-header h2').textContent,/chosen position/);d.querySelector('details summary').click();assert(d.querySelector('details').open);assert.equal(d.querySelectorAll('.katex-error').length,0);assert.deepEqual(errors,[]);
console.log('Standalone magic lab: all 3 demos, card swaps, 8/52-card shuffles, target 52, mobile input, disclosure and English passed');
process.exit(0);
