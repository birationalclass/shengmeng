const {chromium}=require(process.env.PLAYWRIGHT_MODULE||'playwright');
const assert=require('node:assert/strict');
(async()=>{const browser=await chromium.launch({channel:'msedge',headless:true});try{
 const base=process.env.SITE_URL||'http://localhost:4186';
 const page=await browser.newPage({viewport:{width:1756,height:1244}}),errors=[];
 page.on('pageerror',e=>errors.push(e.message));
 for(const lang of ['zh','en']){
  await page.goto(base+'/formalization/negativity/?lang='+lang+'&v=20261002-formal-12#node=localcartier');
  await page.waitForSelector('#evidenceContent .evidence-grid',{state:'attached'});
  const snapshot=await page.evaluate(async()=>await(await fetch('snapshot.json')).json());
  assert.equal(Object.keys(snapshot.declarations).length,121);
  for(const name of ['cartierAtlas_weilCycle_isWeilDivisor','cartierAtlas_weilCycle_eq_of_unit_transitions',
    'exists_cartierAtlas_pullback','exists_realCartier_pullback_pushforward','exists_realCartier_effectivity_descent',
    'geometric_exceptional_iff','weilCycleCoefficients_pushforward']){
   assert(snapshot.declarations[name]);
   assert(snapshot.declarations[name].axioms.every(a=>['propext','Classical.choice','Quot.sound'].includes(a)));
  }
  const type=snapshot.declarations.exists_realCartier_pullback_pushforward.code.split(':= by')[0];
  assert(type.includes('CartierAtlas')&&type.includes('IsProper')&&type.includes('BirationalMorphism'));
  assert(!/\b(hleft|hcoeff|hcompat|hexceptional)\b/.test(type));
  await page.locator('[data-view="2d"]').click();
  await page.locator('#scope').selectOption('path');
  for(const id of ['localcartier','cartierpullback','strict','pushpull','effdown']){
   await page.locator('#editorSelect').selectOption(id);
   assert(await page.locator(`[data-node="${id}"]`).evaluate(e=>e.classList.contains('done')));
   assert.equal(await page.locator('#overviewPanel .dep-link.assumption').count(),0);
   assert((await page.locator('#sourcePanel').innerText()).includes(id==='strict'?'weilCycleCoefficients_pushforward':id==='effdown'?'exists_realCartier_effectivity_descent':id==='pushpull'?'exists_realCartier_pullback_pushforward':id==='cartierpullback'?'exists_cartierAtlas_pullback':'cartierAtlas_weilCycle_isWeilDivisor'));
  }
  const effectivity=await page.locator('#overviewPanel').innerText();
  assert(!effectivity.includes('hleft :'));
  assert(effectivity.includes('CycleEffective (actualPullbackWeilCycle)'));
  await page.locator('#editorSelect').selectOption('projection');
  assert(await page.locator('[data-node="projection"]').evaluate(e=>e.classList.contains('assumption')));
  assert.equal(await page.locator('.curve-stage-open').count(),1);
  await page.locator('#editorSelect').selectOption('chow');
  assert(await page.locator('[data-node="chow"]').evaluate(e=>e.classList.contains('assumption')));
  await page.locator('#editorSelect').selectOption('localcartier');
  await page.locator('#scope').selectOption('direct');
  await page.locator('[data-frame="all"]').click();
  assert(await page.evaluate(()=>document.documentElement.scrollHeight<=innerHeight+1));
  if(lang==='zh')await page.screenshot({path:process.env.SCREENSHOT_PATH||'C:/Users/math1/Documents/Math/output/formalization-site/cartier-verified.png'});
  await page.locator('[data-view="3d"]').click();
  assert.equal(await page.locator('[data-node="localcartier"]').first().getAttribute('aria-pressed'),'true');
 }
 assert.deepEqual(errors,[]);
 console.log('PASS: 121 audited declarations, bilingual actual Cartier construction, real push-pull without hleft/hcoeff, actual strict-transform model bridge, effectivity descent, honest remaining curve/Chow gaps, 2D/3D navigation.');
}finally{await browser.close();}})().catch(e=>{console.error(e);process.exitCode=1;});
