import test from 'node:test';
import assert from 'node:assert/strict';
import {LoadingTransfer,openingPreparationPending} from './loading-transfer.js';
test('entry-ready does not finish the resource meter while required preparation continues',()=>{
 for(const openingPreparation of ['pending','loading',undefined])assert.equal(openingPreparationPending({ready:'true',entered:'false',openingPreparation}),true);
 for(const openingPreparation of ['ready','error'])assert.equal(openingPreparationPending({entered:'false',openingPreparation}),false);
 assert.equal(openingPreparationPending({entered:'true',openingPreparation:'loading'}),false);
});
const base='https://example.test/visuals/math-refuge/';
const fixture=()=>new LoadingTransfer([{url:'app.js',bytes:1000},{url:'assets/field.png',bytes:4000}],base);
test('completed, compressed and cached resources count once; caching produces no download speed',()=>{
 const meter=fixture();const entry={name:base+'app.js?v=1',startTime:5,decodedBodySize:1000,transferSize:400,responseStatus:200};
 meter.observe(entry,1000);meter.observe(entry,1100);assert.equal(meter.snapshot(1100).loaded,1000);assert.equal(meter.snapshot(1100).bytesPerSecond,200);
 meter.observe({name:base+'assets/field.png',startTime:10,decodedBodySize:4000,transferSize:0},1200);
 assert.equal(meter.snapshot(1200).loaded,5000);assert.equal(meter.snapshot(1200).total,5000);assert.equal(meter.snapshot(1200).bytesPerSecond,200);
});
test('stream updates keep byte progress monotone, reconcile completion, then decay to zero',()=>{
 const meter=fixture();meter.progress('assets/field.png',2000,1000);meter.progress('assets/field.png',1000,1100);assert.equal(meter.snapshot(1100).loaded,2000);
 meter.observe({name:base+'assets/field.png',startTime:0,decodedBodySize:4000,transferSize:4300},1500);
 assert.equal(meter.snapshot(1500).loaded,4000);assert.equal(meter.snapshot(1500).bytesPerSecond,2150);assert.equal(meter.snapshot(3600).bytesPerSecond,0);
});
test('foreign APIs, on-demand audio and failed requests cannot inflate the opening total',()=>{
 const meter=fixture();for(const name of ['https://weather.example/api',base+'assets/audio/report.mp3'])meter.observe({name,startTime:1,decodedBodySize:900000,transferSize:900300},1000);
 meter.observe({name:base+'app.js',startTime:5,decodedBodySize:900,transferSize:1200,responseStatus:404},1000);
 assert.equal(meter.snapshot(1000).loaded,0);assert.equal(meter.snapshot(1000).total,5000);
 meter.finish();meter.observe({name:base+'app.js',startTime:5,decodedBodySize:1000,transferSize:1300},2000);assert.equal(meter.snapshot(2000).loaded,0);
});
test('finishing during a failed opening never invents 100 percent downloaded',()=>{
 const meter=fixture();meter.progress('assets/field.png',1500,1000);meter.finish();assert.equal(meter.snapshot(1000).loaded,1500);assert.equal(meter.snapshot(1000).bytesPerSecond,0);
});
test('directory navigation counts the HTML and buffered old requests do not pretend to be current traffic',()=>{
 const meter=new LoadingTransfer([{url:'index.html',bytes:500}],base);
 meter.observe({name:base,startTime:0,responseEnd:100,decodedBodySize:500,transferSize:800},5000);
 assert.equal(meter.snapshot(5000).loaded,500);assert.equal(meter.snapshot(5000).bytesPerSecond,0);
});
test('a slow streamed request never recounts chunks that have aged out of the speed window',()=>{
 const meter=fixture();meter.progress('assets/field.png',2000,1000);meter.snapshot(3500);
 meter.progress('assets/field.png',4000,4000);meter.observe({name:base+'assets/field.png',startTime:0,responseEnd:4200,decodedBodySize:4000,transferSize:4300},4200);
 assert.equal(meter.snapshot(4200).bytesPerSecond,1150);
});
