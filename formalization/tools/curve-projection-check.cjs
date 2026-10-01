const {chromium}=require(process.env.PLAYWRIGHT_MODULE||'playwright');
const assert=require('node:assert/strict');
(async()=>{const browser=await chromium.launch({channel:'msedge',headless:true});try{
 const page=await browser.newPage({viewport:{width:1773,height:1244}}), errors=[];
 page.on('pageerror',e=>errors.push(e.message));
 const base=process.env.SITE_URL||'http://localhost:4186';
 for(const lang of ['zh','en']) {
  await page.goto(base+'/formalization/negativity/?lang='+lang+'&v=20261002-formal-10#node=projection');
  await page.waitForSelector('#evidenceContent .evidence-grid',{state:'attached'});
  const panel=page.locator('#overviewPanel .curve-diagram-panel');
  await panel.waitFor({state:'visible'});
  assert.deepEqual(await panel.locator('svg .curve-square-objects text').allTextContents(),['Γ','X′','C','X']);
  assert.deepEqual(await panel.locator('svg .curve-square-maps text').allTextContents(),['i','j','h','π']);
  assert.equal(await panel.locator('.curve-stage-done').count(),2);
  assert.equal(await panel.locator('.curve-stage-open').count(),1);
  assert((await panel.innerText()).includes(lang==='zh'?'全局线丛次数公式：尚待完成':'Global line-bundle degree: still open'));
  assert(await page.locator('[data-node="projection"]').evaluate(e=>e.classList.contains('assumption')));
  await panel.locator('[data-select="pullbackdiagram"]').click();
  assert.equal(await page.locator('#overviewPanel svg.curve-square').count(),1);
  assert((await page.locator('#sourcePanel').innerText()).includes('curve_square_pullback_iso'));
  const pullback=await page.locator('#sourcePanel .source-code').first().innerText();
  assert(pullback.includes('pullbackComp')&&pullback.includes('pullbackCongr'));
  for(const [id,name] of [['curveorder','heightOneOrder_pullback'],['curvefiberdegree','finite_flat_fiber_functionField_degree'],['localprojection','finite_flat_order_fiber_degree'],['principaldivisor','affinePrincipalDivisor_effective_iff'],['pointtensor','finite_flat_point_pullback_degree_over_base'],['closedpoint','finiteType_exists_closedPoint_outside_support'],['localidempotents','localRing_idempotent_trivial']]){
   await page.locator('#editorSelect').selectOption(id);
   assert(await page.locator('[data-node="'+id+'"]').evaluate(e=>e.classList.contains('done')));
   const source=await page.locator('#sourcePanel').innerText();
   assert(source.includes(name));assert(!source.includes('hcompat :'));
  }
  await page.locator('#editorSelect').selectOption('strict');
  assert((await page.locator('#overviewPanel').innerText()).includes('coeff'));
  assert((await page.locator('#overviewPanel').innerText()).includes(enLabel(lang,'What “cycle” means here','这里的 cycle 是什么')));
  await page.locator('#editorSelect').selectOption('curves');
  const deps=await page.locator('#overviewPanel .dep-list').first().locator('[data-select]').evaluateAll(es=>es.map(e=>e.dataset.select));
  assert(deps.includes('max')&&deps.includes('closedpoint')&&deps.includes('cover')&&deps.includes('strict'));
  await page.locator('#editorSelect').selectOption('connected');
  assert((await page.locator('#detailHeader').innerText()).includes(enLabel(lang,'not by part (1)','第 (1) 部分')));
  await page.locator('#editorSelect').selectOption('properreduce');
  await page.locator('#scope').selectOption('path');
  const ids=await page.locator('#graph .node:not([hidden])').evaluateAll(es=>es.map(e=>e.dataset.node));
  for(const id of ['connected','fiber','projective2','localidempotents','fiberdown'])assert(!ids.includes(id),'Part (1) depends on the part (2) branch: '+id);
  assert(await page.evaluate(()=>document.documentElement.scrollHeight<=innerHeight+1));
 }
 await page.setViewportSize({width:390,height:844});
 await page.goto(base+'/formalization/negativity/?lang=zh#node=projection');
 await page.waitForSelector('#evidenceContent .evidence-grid',{state:'attached'});
 if(!await page.locator('#overviewPanel .curve-diagram-panel').isVisible())await page.locator('#editorSelect').selectOption('projection');
 await page.locator('#overviewPanel .curve-diagram-panel').waitFor({state:'visible'});
 const r=await page.locator('svg.curve-square').evaluate(e=>({w:e.getBoundingClientRect().width,left:e.getBoundingClientRect().left,right:e.getBoundingClientRect().right}));
 assert(r.w>200 && r.left>=0 && r.right<=390);
 assert.deepEqual(errors,[]);
 if(process.env.SCREENSHOT){await page.setViewportSize({width:1773,height:1244});await page.goto(base+'/formalization/negativity/?lang=zh#node=projection');await page.waitForSelector('#evidenceContent .evidence-grid',{state:'attached'});await page.screenshot({path:process.env.SCREENSHOT});}
 console.log('PASS: bilingual square, tensor point counting, actual closed-point and local-ring proofs, precise prime-divisor pushforward, independent part (1), honest open global degree, mobile SVG.');
}finally{await browser.close();}})().catch(e=>{console.error(e);process.exitCode=1;});
function enLabel(lang,en,zh){return lang==='en'?en:zh;}
