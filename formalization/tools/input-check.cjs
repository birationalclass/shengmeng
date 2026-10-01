const {chromium}=require(process.env.PLAYWRIGHT_MODULE||'playwright');
const assert=require('node:assert/strict');
(async()=>{const b=await chromium.launch({channel:'msedge',headless:true});try{
 const p=await b.newPage({viewport:{width:1440,height:900}}),errors=[];p.on('pageerror',e=>errors.push(e.message));
 const base=process.env.SITE_URL||'http://localhost:4186';
 for(const lang of ['en','zh']){
  await p.goto(base+'/formalization/negativity/?lang='+lang+'#node=effdown');
  await p.waitForSelector('#evidenceContent .evidence-grid',{state:'attached'});
  let text=await p.locator('#overviewPanel').innerText();
  assert(text.includes('hleft : AlgebraicCycle.map π wx wy lifted = D'));
  assert(text.includes('hlifted : CycleEffective lifted'));
  assert(text.includes('scheme_cycle_map_effective'));
  const depIds=await p.locator('#overviewPanel .dep-list').first().locator('[data-select]').evaluateAll(es=>es.map(e=>e.dataset.select));
  assert.deepEqual(depIds,['geomcycle','pushpull']);
  assert((await p.locator('#sourcePanel').innerText()).includes('scheme_effective_descends'));
  await p.locator('#editorSelect').selectOption('projection');
  text=await p.locator('#overviewPanel').innerText();assert(text.includes('hcompat : up (single x 1)'));
  assert(!text.includes("degree' c' (pull D) = 0 ∨"));
  await p.locator('#editorSelect').selectOption('projectioncases');
  assert((await p.locator('#sourcePanel').innerText()).includes('projection_cases_from_cycle_push'));
  await p.locator('#editorSelect').selectOption('realspan');
  assert((await p.locator('#sourcePanel').innerText()).includes('projection_formula_on_real_span'));
  await p.locator('#editorSelect').selectOption('localorder');
  assert((await p.locator('#sourcePanel').innerText()).includes('dvr_order_ringEquiv'));
  await p.locator('#editorSelect').selectOption('pushpullcriterion');
  const criterion=await p.locator('#sourcePanel .source-code').first().innerText();
  assert(criterion.includes('scheme_pushpull_of_local_isomorphisms'));
  assert(criterion.includes('(hstalk :'));
  assert(!criterion.includes('(hleft :'),'The local push-pull criterion must derive, not assume, hleft');
 }
 assert.deepEqual(errors,[]);console.log('PASS: exact remaining inputs, proved effectivity dependency, actual cycle descent source, Cartier compatibility, bilingual span/case navigation.');
}finally{await b.close();}})().catch(e=>{console.error(e);process.exitCode=1;});
