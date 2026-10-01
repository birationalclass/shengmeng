const {chromium}=require(process.env.PLAYWRIGHT_MODULE||'playwright');
const assert=require('node:assert/strict');
(async()=>{const browser=await chromium.launch({channel:'msedge',headless:true});try{
 const base=process.env.SITE_URL||'http://localhost:4186';
 const page=await browser.newPage({viewport:{width:1756,height:1244}}),errors=[];
 page.on('pageerror',e=>errors.push(e.message));
 for(const lang of ['zh','en']){
  await page.goto(base+'/formalization/negativity/?lang='+lang+'#node=codimone');
  await page.waitForSelector('#evidenceContent .evidence-grid',{state:'attached'});
  const snapshot=await page.evaluate(async()=>await(await fetch('snapshot.json')).json());
  assert.equal(Object.keys(snapshot.declarations).length,93);
  for(const name of ['proper_birational_isIso_on_codimensionOne_open','proper_birational_codimensionOne_unique_preimage','hartshorne_graph_closure','rationalFunction_principal_degree_zero','normal_affine_sections'])
   assert(snapshot.declarations[name]&&!snapshot.declarations[name].axioms.includes('sorryAx'));
  await page.locator('[data-view="2d"]').click();
  await page.locator('#scope').selectOption('path');
  assert(await page.locator('[data-node="codimone"]').evaluate(e=>e.classList.contains('done')));
  assert.equal(await page.locator('#overviewPanel .dep-link.assumption').count(),0);
  const source=await page.locator('#sourcePanel').innerText();
  assert(source.includes('proper_birational_isIso_on_codimensionOne_open'));
  assert(source.includes('hnormal')&&source.includes('BirationalMorphism'));
  assert(source.includes('IsProper')&&!source.includes('(hIso :'));
  await page.locator('#editorSelect').selectOption('cover');
  const cover=await page.locator('#overviewPanel').innerText();
  assert(cover.includes('quasi-finite'));
  assert(lang==='zh'?cover.includes('闭点')&&cover.includes('局部维数'):cover.includes('closed point')&&cover.includes('local fiber dimension'));
  assert(await page.locator('[data-node="cover"]').evaluate(e=>e.classList.contains('assumption')));
  await page.locator('#editorSelect').selectOption('chow');
  assert(await page.locator('[data-node="chow"]').evaluate(e=>e.classList.contains('assumption')));
  await page.locator('#editorSelect').selectOption('hartshornegraph');
  assert((await page.locator('#sourcePanel').innerText()).includes('graph.image'));
  await page.locator('#editorSelect').selectOption('projection');
  assert.equal(await page.locator('.curve-stage-open').count(),1);
  const projection=await page.locator('#overviewPanel').innerText();
  assert(lang==='zh'?projection.includes('范数'):projection.includes('norm/valuation'));
  await page.locator('#editorSelect').selectOption('relativesigns');
  assert((await page.locator('#sourcePanel').innerText()).includes('contracted'));
  await page.locator('#editorSelect').selectOption('codimone');
  await page.locator('#scope').selectOption('direct');
  await page.locator('[data-frame="all"]').click();
  assert(await page.evaluate(()=>document.documentElement.scrollHeight<=innerHeight+1));
  if(lang==='zh')await page.screenshot({path:process.env.SCREENSHOT_PATH||'C:/Users/math1/Documents/Math/output/formalization-site/codimension-one-verified.png'});
 }
 assert.deepEqual(errors,[]);
 console.log('PASS: bilingual actual codimension-one proof, 93 audited declarations, precise closed-point coverage, honest Chow/degree gaps and relative curve signs.');
}finally{await browser.close();}})().catch(e=>{console.error(e);process.exitCode=1;});
