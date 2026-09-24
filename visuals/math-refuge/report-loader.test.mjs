import test from 'node:test';
import assert from 'node:assert/strict';
import {createReportLoader} from './report-loader.js';

test('report preparation shares requests, reuses the cover, and retries a failed load',async()=>{
  const originalFetch=globalThis.fetch,OriginalImage=globalThis.Image;
  let requests=0,images=0,fail=true;
  globalThis.fetch=async()=>{requests++;return {ok:!fail,text:async()=>JSON.stringify({pages:[{formulaAsset:'cover.svg'}]})};};
  globalThis.Image=class{set src(url){images++;assert.equal(url,'cover.svg?v62-chalk-ink');queueMicrotask(()=>this.onload());}};
  try{
    const prepare=createReportLoader(),report={id:'test',manifest:'pages.json'};
    const failed=prepare(report);assert.equal(prepare(report),failed);await assert.rejects(failed);
    fail=false;
    const prepared=prepare(report);assert.equal(prepare(report),prepared);
    const result=await prepared;assert.equal((await prepare(report)).cover,result.cover);
    assert.equal(requests,2);assert.equal(images,1);
  }finally{globalThis.fetch=originalFetch;globalThis.Image=OriginalImage;}
});
