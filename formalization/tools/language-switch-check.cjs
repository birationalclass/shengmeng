const {chromium}=require(process.env.PLAYWRIGHT_MODULE||'playwright');
const assert=require('node:assert/strict');
(async()=>{const browser=await chromium.launch({channel:'msedge',headless:true});try{
 let page;const errors=[];let documents=0;
 const base=process.env.SITE_URL||'http://localhost:4186';
 for(const initial of ['zh','en']){
  if(page)await page.close();page=await browser.newPage({viewport:{width:1756,height:1244}});
  page.on('pageerror',e=>errors.push(e.message));page.on('request',r=>{if(r.resourceType()==='document'&&r.isNavigationRequest())documents++;});
  await page.goto(base+'/formalization/negativity/?lang='+initial+'&v=20261002-lang-3#node=codimone');
  await page.waitForSelector('#evidenceContent .evidence-grid',{state:'attached'});
  await page.locator('[data-view="2d"]').click();await page.locator('#scope').selectOption('direct');
   await page.waitForFunction(()=>document.querySelector('.graph-scroll').dataset.cameraMoving!=='true');
  await page.locator('[data-frame="theorem"]').click();
  await page.waitForTimeout(60);
  await page.locator('.theorem-target-card[data-theorem-card="2d"] .theorem-target-toggle').click();
  await page.waitForFunction(()=>document.querySelector('.theorem-target-card[data-theorem-card="2d"] .theorem-target-toggle').getAttribute('aria-expanded')==='false');
  await page.locator('[data-frame="selected"]').click();await page.locator('.input-rail-toggle').click();
  await page.locator('#stepsTab').click();await page.locator('#nextStep').click();
  const before=await page.locator('[data-node="codimone"]').boundingBox(),zoom=await page.locator('.editor-navigation output').innerText();
  const count=documents,identity=await page.evaluate(()=>performance.timeOrigin),statuses=await page.locator('[data-status-count]').allTextContents();
  for(let i=0;i<4;i++){
   await page.locator('#languageToggle').click();const en=(initial==='zh')===(i%2===0);
   await page.waitForFunction(en=>document.documentElement.lang===(en?'en':'zh-CN'),en);
   assert.equal(await page.locator('#detailHeader h2').innerText(),en?'Codimension-one isomorphism over a normal base':'正规底上余维一处同构');
   assert.equal(await page.locator('[data-node="codimone"] .node-heading').innerText(),en?'Codimension-one isomorphism over a normal base':'正规底上余维一处同构');
   assert.match(await page.locator('.theorem-target-status').first().innerText(),en?/Complete theorem/:/完整定理/);
   assert.equal(await page.locator('.input-rail-toggle').innerText(),en?'Stack cards':'折叠纸牌');
   assert.equal(await page.locator('[data-frame="theorem"]').innerText(),en?'Theorem':'最终定理');
   assert.equal(await page.locator('[data-node-zoom="in"]').getAttribute('aria-label'),en?'Zoom in':'放大');
   assert.equal(await page.locator('.input-rail-toggle').getAttribute('aria-expanded'),'true');
   assert.equal(await page.locator('.theorem-target-card[data-theorem-card="2d"] .theorem-target-toggle').getAttribute('aria-expanded'),'false');
   assert.equal(await page.locator('#stepsTab').getAttribute('aria-selected'),'true');
   assert.match(await page.locator('.stepper span').innerText(),/^2\s*\//);
   assert.equal(await page.locator('#scope').inputValue(),'direct');
   assert.equal(await page.locator('#editorSelect').inputValue(),'codimone');
   assert.equal(await page.locator('.editor-navigation output').innerText(),zoom);
   const after=await page.locator('[data-node="codimone"]').boundingBox();
   assert(Math.abs(after.x-before.x)<1&&Math.abs(after.y-before.y)<1&&Math.abs(after.width-before.width)<1,'Language switch moved the 2D camera');
   assert.equal(documents,count,'Language switch navigated the document');assert.equal(await page.evaluate(()=>performance.timeOrigin),identity);
   assert.deepEqual(await page.locator('[data-status-count]').allTextContents(),statuses);
   assert.equal(new URL(page.url()).searchParams.get('lang'),en?'en':'zh');
   assert.equal(new URL(page.url()).hash,'#node=codimone');
   if(process.env.SCREENSHOT_PATH&&initial==='zh'&&i===0)await page.screenshot({path:process.env.SCREENSHOT_PATH});
  }
  await page.locator('[data-view="3d"]').click();await page.locator('[data-camera="focus"]').click();
  await page.locator('.spatial-stage').focus();await page.keyboard.press('ArrowRight');await page.keyboard.press('+');
  await page.waitForTimeout(80);const camera=await page.locator('[data-spatial-node="codimone"]').boundingBox();
  await page.locator('#languageToggle').click();await page.waitForTimeout(80);
  assert.equal(await page.locator('[data-view="3d"]').getAttribute('aria-pressed'),'true');
  assert.equal(await page.locator('[data-camera="focus"]').getAttribute('aria-pressed'),'true');
  const after3d=await page.locator('[data-spatial-node="codimone"]').boundingBox();
  assert(['x','y','width','height'].every(k=>Math.abs(after3d[k]-camera[k])<1),'Language switch moved the 3D camera');
  assert.equal(documents,count);
 }
 await page.goto(base+'/formalization/?lang=zh&v=20261002-lang-3');const count=documents;
 await page.locator('#languageToggle').click();assert.equal(await page.locator('html').getAttribute('lang'),'en');assert.equal(documents,count);
 await page.locator('#languageToggle').click();assert.equal(await page.locator('html').getAttribute('lang'),'zh-CN');assert.equal(documents,count);
 assert.deepEqual(errors,[]);console.log('PASS: no document reload in either language or hub; selection, zoom, 2D/3D camera, scopes, tabs, proof step, spread state, theorem collapse, URL and proof counts preserved.');
}finally{await browser.close();}})().catch(e=>{console.error(e);process.exitCode=1;});
