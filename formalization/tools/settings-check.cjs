const {chromium}=require(process.env.PLAYWRIGHT_MODULE||'playwright');
const assert=require('node:assert/strict');
(async()=>{const b=await chromium.launch({channel:'msedge',headless:true});try{
const p=await b.newPage({viewport:{width:1440,height:900}}),errors=[];p.on('pageerror',e=>errors.push(e.message));
const base=process.env.SITE_URL||'http://localhost:4186';
await p.goto(base+'/formalization/negativity/?lang=en#node=cover');
await p.waitForSelector('#settingsToggle');await p.locator('[data-view="2d"]').click();
await p.locator('#settingsToggle').click();await p.locator('#resetTypography').click();
async function set(key,value){await p.locator('#font-'+key).evaluate((e,v)=>{e.value=v;e.dispatchEvent(new Event('input',{bubbles:true}));},String(value));}
await set('node',24);await set('detail',22);await set('ui',16);await set('width',440);
assert.equal(await p.locator('#value-node').innerText(),'24 px');await p.locator('#closeSettings').click();
assert.equal(await p.evaluate(()=>getComputedStyle(document.documentElement).getPropertyValue('--detail-base-font')),'22px');
const glyph=()=>p.locator('[data-node="cover"] .node-heading').evaluate(e=>parseFloat(getComputedStyle(e).fontSize));
const size=await glyph();await p.locator('[data-node-zoom="in"]').click();assert(await glyph()>size,'Zoom must increase actual font size');
assert.equal(await p.locator('#graph').evaluate(e=>getComputedStyle(e).transform),'none');
await p.reload();await p.waitForSelector('#settingsToggle');await p.locator('#settingsToggle').click();assert.equal(await p.locator('#font-node').inputValue(),'24');assert.equal(await p.locator('#font-detail').inputValue(),'22');await p.locator('#closeSettings').click();
await p.locator('#editorSelect').selectOption('projection');await p.waitForTimeout(150);assert((await p.locator('#detail').innerText()).includes('Required identity'));assert((await p.locator('#detail').innerText()).includes('π'));
await p.locator('[data-view="3d"]').click();await p.waitForTimeout(150);
assert(!(await p.locator('.spatial-node').first().getAttribute('style')).includes('scale('),'3D text must not use scaled layers');
await p.screenshot({path:'D:/codex/Math/output/lean-visualization-references/font-settings-desktop.png'});
await p.locator('#settingsToggle').click();await p.screenshot({path:'D:/codex/Math/output/lean-visualization-references/font-settings-panel.png'});
await set('node',26);await set('detail',24);await set('ui',18);await set('width',560);await p.locator('#closeSettings').click();
await p.setViewportSize({width:390,height:844});await p.waitForTimeout(200);
assert(await p.evaluate(()=>document.documentElement.scrollWidth<=innerWidth&&document.documentElement.scrollHeight<=innerHeight+1),'Settings must not cause document overflow');
await p.locator('#settingsToggle').click();await p.locator('#resetTypography').click();await p.locator('#closeSettings').click();
await p.goto(base+'/formalization/negativity/?lang=zh#node=cover');await p.waitForSelector('#settingsToggle');await p.locator('#settingsToggle').click();assert((await p.locator('.typography-settings').innerText()).includes('节点字号'));
assert.deepEqual(errors,[]);console.log('PASS: font sizes, persistence, reset, sharp 2D/3D rendering, bilingual settings, mobile overflow, explicit projection target.');
}finally{await b.close();}})().catch(e=>{console.error(e);process.exitCode=1;});
