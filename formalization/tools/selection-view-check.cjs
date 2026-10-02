const {chromium}=require(process.env.PLAYWRIGHT_MODULE||'playwright');
const assert=require('node:assert/strict');
(async()=>{const browser=await chromium.launch({channel:'msedge',headless:true});try{
 const page=await browser.newPage(),errors=[];page.on('pageerror',e=>errors.push(e.message));
 const base=process.env.SITE_URL||'http://localhost:4186';
 const zoom=()=>page.locator('.editor-navigation output').innerText();
 const box=id=>page.locator(`[data-node="${id}"]`).boundingBox();
 for(const size of [{width:1756,height:1244},{width:1280,height:720},{width:390,height:844}]){
  await page.setViewportSize(size);
  for(const lang of ['zh','en']){
   if(size.width<=760)await page.setViewportSize({width:1280,height:720});
   await page.goto(base+'/formalization/negativity/?lang='+lang+'&v=20261002-view-2#node=projection');
   await page.waitForSelector('#evidenceContent .evidence-grid',{state:'attached'});
   await page.locator('[data-view="2d"]').click();await page.locator('#scope').selectOption('direct');
   await page.waitForFunction(()=>document.querySelector('.graph-scroll').dataset.cameraMoving!=='true');
   if(size.width<=760)await page.setViewportSize(size);
   await page.locator('[data-frame="selected"]').click();
   let before=await box('projection'),scale=await zoom();
   for(let i=0;i<4;i++){
    await page.locator('.input-rail-toggle').click();
    const after=await box('projection');
    assert.equal(await zoom(),scale,'Spread/collapse changed the zoom');
    assert(Math.abs(after.x-before.x)<1&&Math.abs(after.y-before.y)<1,'Spread/collapse moved the selected card');
    assert.equal(await page.locator('.input-rail-toggle').getAttribute('aria-expanded'),String(i%2===0));
   }
   await page.locator('#editorSelect').selectOption('codimone');
   await page.waitForFunction(()=>document.querySelector('.graph-scroll').dataset.cameraMoving!=='true');
   const selected=await box('codimone'),view=await page.locator('.graph-scroll').boundingBox();
   assert.equal(await zoom(),scale,'Selection changed the zoom');
   assert(selected.x>=view.x+19&&selected.x+selected.width<=view.x+view.width-19,'Selected card is outside safe horizontal margins');
   if(size.width>760)assert((selected.x+selected.width/2-view.x)/view.width>=.64,'Result should leave space for premises on its left');
   assert.equal(await page.locator('[data-node="codimone"]').getAttribute('aria-pressed'),'true');
   const first=await box('dvrfoundation');
   assert(first.x<selected.x,'Premise should remain to the left');
   // Selecting via a graph card uses the same camera behavior as the dropdown.
   await page.locator('[data-frame="selected"]').click();
   scale=await zoom();await page.locator('[data-node="dvrfoundation"] .node-heading').click();
   await page.waitForFunction(()=>document.querySelector('.graph-scroll').dataset.cameraMoving!=='true');
   assert.equal(await zoom(),scale);assert.equal(await page.locator('[data-node="dvrfoundation"]').getAttribute('aria-pressed'),'true');
   const root=await box('dvrfoundation');
   assert(root.x>=view.x+19&&root.x+root.width<=view.x+view.width-19);
   await page.locator('#editorSelect').selectOption('codimone');
   await page.waitForFunction(()=>document.querySelector('.graph-scroll').dataset.cameraMoving!=='true');
   if(size.width===1756&&lang==='zh')await page.screenshot({path:process.env.SCREENSHOT_PATH||'C:/Users/math1/Documents/Math/tmp/proof-settings/selection-view.png'});
   // A filter change should preserve the selected card's anchor.
   if(size.width>760){before=await box('codimone');scale=await zoom();await page.locator('#scope').selectOption('path');
   await page.waitForFunction(()=>document.querySelector('.graph-scroll').dataset.cameraMoving!=='true');
    const after=await box('codimone');assert.equal(await zoom(),scale);
    assert(Math.abs(after.x-before.x)<1&&Math.abs(after.y-before.y)<1);}
   assert(await page.evaluate(()=>document.documentElement.scrollHeight<=innerHeight+1&&document.documentElement.scrollWidth<=innerWidth));
  }
 }
 assert.deepEqual(errors,[]);console.log('PASS: bilingual desktop/mobile spread/collapse keeps zoom and selected anchor; card/dropdown selections pan into reading position; scope changes preserve camera; no outer scrolling.');
}finally{await browser.close();}})().catch(e=>{console.error(e);process.exitCode=1;});
