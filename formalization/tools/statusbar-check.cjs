const {chromium}=require(process.env.PLAYWRIGHT_MODULE),assert=require('node:assert/strict');
const out=process.env.SCREENSHOT_DIR;
const base=process.env.SITE_URL||'http://localhost:4186';
(async()=>{const b=await chromium.launch({channel:'msedge',headless:true});try{const p=await b.newPage({viewport:{width:1756,height:1244}}),errors=[];p.on('pageerror',e=>errors.push(e.message));await p.goto(base+'/formalization/negativity/?lang=zh#node=localcartier');await p.waitForSelector('.atlas-statusbar .status-count');await p.waitForFunction(()=>document.querySelector('.graph-scroll').dataset.cameraMoving!=='true');
const counts=await p.locator('[data-status-count]').allTextContents();assert.equal(await p.locator('.atlas-heading,.graph-note,#release').count(),0);
assert.equal(await p.locator('.refuge-back').getAttribute('href'),'../../');assert.equal(await p.locator('.refuge-back span').innerText(),'主页');
const red=await p.locator('.completion-status').evaluate(e=>({color:getComputedStyle(e).color,hidden:e.hidden}));assert.equal(red.color,'rgb(178, 56, 73)');assert(!red.hidden);
const footer=await p.locator('footer').boundingBox();assert(Math.abs(footer.y+footer.height-1244)<2);assert.equal(await p.locator('footer #expandGraph').count(),1);
await p.locator('#expandGraph').click();assert(await p.locator('.atlas').evaluate(e=>e.classList.contains('expanded')));await p.locator('#expandGraph').click();
await p.locator('[data-frame="selected"]').click();await p.waitForTimeout(80);
const rim=p.locator('#graph [data-node="localcartier"] .dependency-current-halo');await rim.evaluate(e=>{for(const a of e.getAnimations({subtree:true})){a.pause();a.currentTime=+e.dataset.arrival+8200;}});
if(out)await p.screenshot({path:out+'/continuous-statusbar-desktop.png'});
if(out)await p.screenshot({path:out+'/continuous-rim-card.png',clip:await p.locator('#graph [data-node="localcartier"]').boundingBox()});
await p.evaluate(()=>window.__documentIdentity='unchanged');await p.locator('#languageToggle').click();assert.equal(await p.evaluate(()=>window.__documentIdentity),'unchanged');assert.equal(await p.locator('.refuge-back span').innerText(),'Home');assert.deepEqual(await p.locator('[data-status-count]').allTextContents(),counts);assert((await p.locator('.completion-status').innerText()).includes('not yet formalized'));
if(out)await p.screenshot({path:out+'/continuous-statusbar-english.png'});
for(const lang of ['en','zh']){if(lang==='zh')await p.locator('#languageToggle').click();await p.setViewportSize({width:390,height:844});await p.waitForTimeout(80);const q=await p.locator('footer').boundingBox();assert(Math.abs(q.y+q.height-844)<2);assert(await p.locator('footer .pill').evaluateAll(es=>es.every(e=>getComputedStyle(e).display!=='none')));assert(await p.evaluate(()=>document.documentElement.scrollWidth<=innerWidth&&document.documentElement.scrollHeight<=innerHeight+1));if(out)await p.screenshot({path:out+'/continuous-statusbar-mobile-'+lang+'.png'});}
assert.deepEqual(errors,[]);console.log('PASS: home identity and link, removed metadata/header, bottom verification counts and expand action, red incomplete warning, no-refresh bilingual switch, desktop/mobile layout and no outer scrolling.');
}finally{await b.close();}})().catch(e=>{console.error(e);process.exit(1);});
