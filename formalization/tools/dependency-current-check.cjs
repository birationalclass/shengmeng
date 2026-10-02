const {chromium}=require(process.env.PLAYWRIGHT_MODULE||'playwright');
const assert=require('node:assert/strict');
const root=process.env.SCREENSHOT_DIR;
const site=process.env.SITE_URL||'http://localhost:4186';
const version=process.env.RELEASE_QUERY||'20261002-continuous-1';
const screenshotPrefix=process.env.SCREENSHOT_PREFIX||'dependency-current';
(async()=>{
 const browser=await chromium.launch({channel:'msedge',headless:true});
 try{
  const page=await browser.newPage({viewport:{width:1756,height:1244}}),errors=[];
  page.on('pageerror',e=>errors.push(e.message));
  for(const lang of ['zh','en']){
   await page.goto(site+'/formalization/negativity/?lang='+lang+'&v='+version+'#node=normalfinite');
   await page.waitForSelector('#edges .dependency-current-core',{state:'attached'});
   assert.equal(await page.locator('.legend .pill.pending').count(),0);
   assert.match(await page.locator('.completion-status').innerText(),lang==='en'?/not yet formalized/:/尚未/);
   assert((await page.locator('script[src^="app.js"]').getAttribute('src')).includes(process.env.APP_RELEASE||'20261002-statusbar-1'));
   assert.equal(await page.locator('link[href*="dependency-current.css?v=20261002-continuous-1"]').count(),1);
   await page.locator('#scope').selectOption('path');
   await page.waitForFunction(()=>document.querySelector('.graph-scroll').dataset.cameraMoving!=='true');
   const countsBefore=await page.locator('[data-status-count]').allTextContents();
   const edgesBefore=await page.locator('#edges .edge').count();
   const visible=page.locator('#edges .dependency-current-core');
   assert(await visible.count()>0);
   const routes=await page.locator('#edges .dependency-current-core').evaluateAll(es=>es.map(e=>({
    d:e.getAttribute('d'),sourceD:e.parentElement.querySelector('.edge').getAttribute('d'),
    animations:e.getAnimations().length,frames:e.getAnimations()[0]?.effect.getKeyframes().map(k=>k.strokeDashoffset)})));
   assert(routes.every(r=>r.d===r.sourceD&&r.animations===1));
   assert(routes.every(r=>r.frames.includes('12')&&r.frames.includes('-100')));
   const zoom=await page.locator('.editor-navigation output').innerText();
   await page.locator('#editorSelect').selectOption('localcartier');
   await page.waitForFunction(()=>document.querySelector('.graph-scroll').dataset.cameraMoving!=='true');
   await page.waitForFunction(()=>document.querySelector('#edges .dependency-current-core')?.getAnimations().length===1);
   assert.equal(await page.locator('.editor-navigation output').innerText(),zoom);
   const styles=await page.locator('.dependency-current-core').first().evaluate(e=>({dash:getComputedStyle(e).strokeDasharray,stroke:getComputedStyle(e).stroke}));
   assert(styles.dash.includes('12')&&styles.stroke.includes('239, 251, 255'));
   // All pulses share an epoch; downstream steps start after upstream arrivals.
   const timings=await page.locator('#edges .dependency-current-core').evaluateAll(es=>es.map(e=>({
    from:e.parentElement.querySelector('.edge').dataset.from,to:e.parentElement.querySelector('.edge').dataset.to,
    epoch:e.getAnimations()[0]?.startTime,frames:e.getAnimations()[0]?.effect.getKeyframes()})));
   assert(new Set(timings.map(t=>t.epoch)).size===1);
   for(const upstream of timings) for(const downstream of timings) if(upstream.to===downstream.from){
    assert(upstream.frames[4].offset<downstream.frames[1].offset,'No transit time for the intermediate card');
   }
   const transit=await page.locator('#graph .dependency-current-halo[data-flow-mode="transit"]').evaluateAll(es=>es.map(e=>{
    const paths=[...e.querySelectorAll('.dependency-card-core')].filter(p=>getComputedStyle(p).display!=='none');
    const points=paths.map(p=>{const length=p.getTotalLength();return {route:p.dataset.route,start:((q)=>({x:q.x,y:q.y}))(p.getPointAtLength(0)),next:((q)=>({x:q.x,y:q.y}))(p.getPointAtLength(length*.025)),end:((q)=>({x:q.x,y:q.y}))(p.getPointAtLength(length))};});
    return {points,dwell:+e.dataset.departure-e.dataset.arrival,epochs:e.getAnimations({subtree:true}).map(a=>a.startTime)};
   }));
   assert(transit.length>0);
   assert(transit.every(t=>t.dwell===900&&t.points.length===2&&new Set(t.epochs).size===1));
   for(const t of transit){const upper=t.points.find(p=>p.route==='upper'),lower=t.points.find(p=>p.route==='lower');
    assert(upper.next.y<upper.start.y&&lower.next.y>lower.start.y);
    assert.deepEqual(upper.start,lower.start);assert.deepEqual(upper.end,lower.end);
   }
   const halo=page.locator('#graph [data-node="localcartier"] .dependency-current-halo');
   assert.equal(await halo.getAttribute('data-flow-mode'),'orbit');
   const terminal=await halo.evaluate(e=>{const p=e.querySelector('[data-route="orbit"].dependency-card-core'),length=p.getTotalLength();return {
    d:p.getAttribute('d'),duration:e.querySelector('.dependency-orbit-rim').getAnimations()[0].effect.getTiming().duration,display:getComputedStyle(p).display,
    start:((q)=>({x:q.x,y:q.y}))(p.getPointAtLength(0)),next:((q)=>({x:q.x,y:q.y}))(p.getPointAtLength(length*.02)),
    other:[...e.querySelectorAll('.dependency-card-core')].filter(q=>q!==p).map(q=>getComputedStyle(q).display),
    filter:getComputedStyle(e).filter,border:parseFloat(getComputedStyle(e.parentElement,'::after').paddingLeft)};});
   assert(terminal.d.endsWith('Z')&&terminal.duration===12000&&terminal.next.y<terminal.start.y&&terminal.other.every(d=>d==='none'));
   assert(terminal.filter==='none'&&terminal.border<1);
   const rim=halo.locator('.dependency-orbit-rim');
   const wake=await rim.evaluate(e=>({
     gradient:getComputedStyle(e,'::before').backgroundImage,mask:getComputedStyle(e,'::before').maskComposite,
     filter:getComputedStyle(e).filter,epoch:e.getAnimations()[0].startTime,
     frames:e.getAnimations()[0].effect.getKeyframes().map(k=>parseFloat(k['--dependency-flow-angle']))}));
   assert(wake.gradient.includes('conic-gradient')&&wake.gradient.includes('180deg')&&wake.mask.includes('exclude'));
   assert(wake.filter==='none'&&wake.frames.every((a,i)=>i===0||a>=wake.frames[i-1]));
   assert(Math.abs(wake.frames.at(-1)-wake.frames[0]-360)<.0001,'The closed rim must wrap continuously');
   assert.equal(await halo.locator('.dependency-orbit-thread,.dependency-orbit-bloom').count(),0);
   assert(await halo.locator('[data-route="orbit"]').evaluateAll(es=>es.every(e=>getComputedStyle(e).display==='none')));
   await page.locator('[data-node-zoom="in"]').click();await page.waitForTimeout(80);
   assert.equal(await rim.evaluate(e=>e.getAnimations()[0].startTime),wake.epoch,'Zoom reset the rim phase');
   await page.locator('[data-frame="selected"]').click();
   await page.evaluate(()=>document.querySelectorAll('.dependency-current-core,.dependency-current-glow').forEach(e=>e.getAnimations().forEach(a=>{a.pause();const k=a.effect.getKeyframes();a.currentTime=(k[1].offset+k[3].offset)/2*a.effect.getTiming().duration;})));
   if(root)await page.screenshot({path:root+'/'+screenshotPrefix+'-'+lang+'.png'});
   await page.locator('[data-view="3d"]').click();
   await page.waitForFunction(()=>document.querySelector('.dependency-current-spatial .dependency-current-core')?.getAnimations().some(a=>a.playState==='running'));
   assert((await page.locator('#edges .dependency-current-core').evaluateAll(es=>es.every(e=>e.getAnimations().every(a=>a.playState==='paused')))));
   const dBefore=await page.locator('.dependency-current-spatial .dependency-current-core').first().getAttribute('d');
   await page.locator('.spatial-stage').focus();await page.keyboard.press('ArrowRight');
   await page.waitForFunction(d=>document.querySelector('.dependency-current-spatial .dependency-current-core').getAttribute('d')!==d,dBefore);
   await page.emulateMedia({reducedMotion:'reduce'});
   await page.waitForFunction(()=>[...document.querySelectorAll('.dependency-current-core')].every(e=>e.getAnimations().length===0));
   assert(await page.locator('.dependency-current-core.dependency-current-static').count()>0);
   await page.emulateMedia({reducedMotion:'no-preference'});
   await page.locator('[data-view="2d"]').click();
   await page.locator('#editorSelect').selectOption('core');
   await page.waitForFunction(()=>document.querySelector('.graph-scroll').dataset.cameraMoving!=='true');
   await page.waitForTimeout(80);
   assert.equal(await page.locator('[data-node="core"] .dependency-current-halo').count(),0);
   assert(await page.locator('#edges .dependency-current-blocker').count()>0,'No interrupted wires for assumed inputs');
   const cuts=await page.locator('#edges .dependency-current-blocker').evaluateAll(es=>es.map(e=>{
     const original=e.parentElement.querySelector('.edge'),mask=e.parentElement.querySelector('mask'),length=original.getTotalLength();
     return {fraction:+e.dataset.cutFraction,start:+e.dataset.cutStart,end:+e.dataset.cutEnd,length,
      mask:original.getAttribute('mask'),maskId:mask.id,gap:mask.querySelector('path').getAttribute('stroke-dasharray'),
      stroke:getComputedStyle(original).stroke,opacity:getComputedStyle(original).opacity,
      paths:[...e.parentElement.querySelectorAll('.edge,.wire-shadow,.wire-highlight')].map(p=>({d:p.getAttribute('d'),mask:p.getAttribute('mask')})),
      d:original.getAttribute('d'),strands:e.querySelector('.fracture-strands').getAttribute('d'),
      charge:e.querySelector('.blocked-charge').getAnimations().length,
      halo:document.querySelector('[data-node="'+original.dataset.from+'"] .dependency-current-halo')!==null};}));
   assert(cuts.every(c=>c.fraction===.5&&Math.abs((c.start+c.end)/2-c.length/2)<.01&&c.end>c.start));
   assert(cuts.every(c=>c.mask==='url(#'+c.maskId+')'&&c.paths.every(p=>p.d===c.d&&p.mask===c.mask)));
   assert(cuts.every(c=>c.stroke.includes('atlas-wire-active-metal')&&c.opacity==='1'&&c.strands&&c.charge===1&&!c.halo));
   assert.equal(await page.locator('.blocked-stub,.blocked-tail').count(),0);
   await page.emulateMedia({reducedMotion:'reduce'});await page.waitForTimeout(70);
   assert(await page.locator('.blocked-charge').evaluateAll(es=>es.every(e=>e.getAnimations().length===0)));
   await page.emulateMedia({reducedMotion:'no-preference'});
   await page.locator('[data-view="3d"]').click();await page.waitForTimeout(80);
   assert(await page.locator('.dependency-current-spatial .dependency-current-blocker').count()>0);
   assert(await page.locator('.dependency-current-spatial .broken-wire-metal[mask]').count()>0);
   await page.locator('[data-view="2d"]').click();
   assert.equal(await page.locator('#edges .metal-link.assumed .dependency-current-core').count(),0);
   assert.deepEqual(await page.locator('[data-status-count]').allTextContents(),countsBefore);
   assert.equal(await page.locator('#edges .edge').count(),edgesBefore);
   await page.locator('#editorSelect').selectOption('normalfinite');
   await page.waitForFunction(()=>document.querySelectorAll('#edges mask').length===0);
   assert.equal(await page.locator('#edges .edge[mask]').count(),0);
   assert(await page.evaluate(()=>document.documentElement.scrollHeight<=innerHeight+1));
  }
  assert.deepEqual(errors,[]);
  console.log('Passed split perimeter transit, slow clockwise terminal orbit, original-metal midpoint fracture and mask cleanup, bilingual 2D/3D wire alignment, synchronized staged pulse direction, proof-status/edge preservation, no zoom change, camera tracking, hidden-view pause and reduced motion.');
 }finally{await browser.close();}
})().catch(e=>{console.error(e);process.exit(1);});


