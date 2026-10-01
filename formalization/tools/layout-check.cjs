const {chromium}=require(process.env.PLAYWRIGHT_MODULE||'playwright');
const assert=require('node:assert/strict');
(async()=>{const browser=await chromium.launch({channel:'msedge',headless:true});try{
 const page=await browser.newPage(),errors=[];page.on('pageerror',e=>errors.push(e.message));
 const base=process.env.SITE_URL||'http://localhost:4186';
 for(const size of [{width:1773,height:1244},{width:1280,height:720}]){
  await page.setViewportSize(size);
  for(const lang of ['en','zh']){
   await page.goto(base+'/formalization/negativity/?lang='+lang+'#node=projective2');
   await page.waitForSelector('#evidenceContent .evidence-grid',{state:'attached'});
   await page.locator('[data-view="2d"]').click();
   await page.locator('#scope').selectOption('direct');
   let ids=await page.locator('#graph .node:not([hidden])').evaluateAll(es=>es.map(e=>e.dataset.node).sort());
   assert.deepEqual(ids,['connected','fiber','intersection','projective2']);
   const header=await page.locator('#detailHeader').innerText();
   assert(header.includes('−D')&&header.includes('f-nef'),'The geometric statement omits nefness');
   assert(lang==='en'?header.includes('not used in the effectivity proof'):header.includes('不用于第 (1)'));
   const color=await page.locator('[data-node="projective2"] .node-heading').evaluate(e=>getComputedStyle(e).backgroundColor);
   assert.equal(color,'rgb(68, 73, 80)','Pending heading must match the gray legend');
   const view=await page.locator('.graph-scroll').boundingBox();
   const boxes=await page.locator('#graph .node:not([hidden])').evaluateAll(es=>es.map(e=>{const r=e.getBoundingClientRect();return {id:e.dataset.node,x:r.x,y:r.y,w:r.width,h:r.height}}));
   for(const a of boxes){assert(a.x>=view.x-1&&a.y>=view.y-1&&a.x+a.w<=view.x+view.width+1&&a.y+a.h<=view.y+view.height+1,'Direct view should fit the viewport');}
   for(let i=0;i<boxes.length;i++)for(let j=i+1;j<boxes.length;j++){const a=boxes[i],b=boxes[j];assert(a.x+a.w<=b.x||b.x+b.w<=a.x||a.y+a.h<=b.y||b.y+b.h<=a.y,'Nodes overlap');}
   if(size.width===1773&&lang==='en')await page.screenshot({path:process.env.SCREENSHOT_PATH||'C:/Users/math1/Documents/Math/output/formalization-site/compact-fiber.png'});
   await page.locator('#editorSelect').selectOption('codimone');
   ids=await page.locator('#graph .node:not([hidden])').evaluateAll(es=>es.map(e=>e.dataset.node).sort());
   assert.deepEqual(ids,['codimone','dvrfoundation','valuative']);
   for(const [id,decl] of [['dvrfoundation','normal_one_dimensional_local_isDVR'],['valuative','proper_dvr_lift'],['zmtfinite','proper_quasiFinite_isFinite']]){
    await page.locator('#editorSelect').selectOption(id);
    assert((await page.locator('#sourcePanel').innerText()).includes(decl));
   }
   await page.locator('#editorSelect').selectOption('properreduce');
   await page.locator('#scope').selectOption('path');
   ids=await page.locator('#graph .node:not([hidden])').evaluateAll(es=>es.map(e=>e.dataset.node));
   assert(!ids.includes('fiber')&&!ids.includes('projective2')&&!ids.includes('fiberdown'),'Part (1) depends on the independent fiber-support branch');
   assert(await page.evaluate(()=>document.documentElement.scrollHeight<=innerHeight+1));
  }
 }
 assert.deepEqual(errors,[]);console.log('PASS: compact framed direct view, no overlapping nodes, gray pending headers, bilingual full hypotheses, independent effectivity/fiber branches and new library source navigation.');
}finally{await browser.close();}})().catch(e=>{console.error(e);process.exitCode=1;});
