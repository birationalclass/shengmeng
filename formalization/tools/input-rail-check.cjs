const {chromium}=require(process.env.PLAYWRIGHT_MODULE||'playwright');
const assert=require('node:assert/strict');
(async()=>{const browser=await chromium.launch({channel:'msedge',headless:true});try{
 const page=await browser.newPage({viewport:{width:1773,height:1244}}),errors=[];
 page.on('pageerror',e=>errors.push(e.message));
 const base=process.env.SITE_URL||'http://localhost:4186';
 for(const lang of ['en','zh']){
  await page.goto(base+'/formalization/negativity/?lang='+lang+'#node=valuative');
  await page.waitForSelector('#evidenceContent .evidence-grid',{state:'attached'});
  await page.locator('[data-view="2d"]').click();
  await page.locator('#scope').selectOption('all');
  await page.locator('[data-frame="all"]').click();
  await page.waitForTimeout(100);
  const roots=page.locator('#graph .base-card:not([hidden])');
  assert(await roots.count()>5);
  const boxes=await roots.evaluateAll(es=>es.map(e=>{const r=e.getBoundingClientRect();return {id:e.dataset.node,x:r.x,y:r.y,w:r.width,h:r.height,compact:e.classList.contains('compact-input')}}));
  assert(boxes.every(r=>Math.abs(r.x-boxes[0].x)<1),'Base inputs split into multiple columns');
  const other=await page.locator('#graph .node:not(.base-card):not([hidden])').evaluateAll(es=>es.map(e=>e.getBoundingClientRect().x));
  assert(other.every(x=>x>boxes[0].x+boxes[0].w),'Derived results are not to the right');
  assert(boxes.some((r,i)=>i&&r.y<boxes[i-1].y+boxes[i-1].h),'Compact inputs should overlap slightly');
  for(const box of boxes){assert(await page.evaluate(({x,y,id})=>document.elementFromPoint(x,y)?.closest('[data-node]')?.dataset.node===id,{x:box.x+box.w/2,y:box.y+8,id:box.id}),'Stacked title is not clickable: '+box.id);}
  assert((await page.locator('.base-input-rail').innerText()).includes(lang==='en'?'Base inputs':'基础输入'));
  if(lang==='zh')await page.screenshot({path:'C:/Users/math1/Documents/Math/output/formalization-site/base-input-rail.png'});
  await page.locator('.input-rail-toggle').click();
  assert.equal(await page.locator('.input-rail-toggle').getAttribute('aria-expanded'),'true');
  assert.equal(await page.locator('#graph .compact-input:not([hidden])').count(),0);
  await page.locator('.input-rail-toggle').click();
  const id=boxes.find(r=>r.compact).id;
  await page.locator(`[data-node="${id}"] .node-heading`).click();
  assert.equal(await page.locator(`[data-node="${id}"]`).getAttribute('aria-pressed'),'true');
  assert(!(await page.locator(`[data-node="${id}"]`).evaluate(e=>e.classList.contains('compact-input'))));
  await page.locator('#editorSelect').selectOption('projective2');
  await page.locator('#scope').selectOption('direct');
  assert.equal(await page.locator('#graph .base-card:not([hidden])').count(),2);assert.equal(await page.locator('#graph .base-card:not(.compact-input):not([hidden])').count(),1);await page.locator('.input-rail-toggle').click();assert.equal(await page.locator('#graph .compact-input:not([hidden])').count(),0);await page.locator('.input-rail-toggle').click();
  assert.equal(await page.locator('[data-node="fiber"]').getAttribute('data-base-input'),'false');
  await page.locator('#scope').selectOption('all');
  await page.locator('[data-view="3d"]').click();
  await page.waitForTimeout(100);
  assert(await page.locator('.spatial-compact-input:not([hidden])').count()>5);
  assert(await page.evaluate(()=>document.documentElement.scrollHeight<=innerHeight+1));
 }
 assert.deepEqual(errors,[]);console.log('PASS: one far-left base-input rail, compact overlap with clickable titles, bilingual expand/collapse, selected input expansion, semantic roots and compact 3D.');
}finally{await browser.close();}})().catch(e=>{console.error(e);process.exitCode=1;});
