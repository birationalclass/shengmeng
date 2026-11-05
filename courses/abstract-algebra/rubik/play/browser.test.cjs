const fs=require('node:fs'),assert=require('node:assert/strict'),path=require('node:path'),os=require('node:os');
const output=process.env.CUBE_QA_OUTPUT||path.join(os.tmpdir(),'rubik-order-qa');fs.mkdirSync(output,{recursive:true});
const {chromium}=require('playwright');
const url=process.env.CUBE_LAB_URL||'http://127.0.0.1:8000/courses/abstract-algebra/rubik/play/';
(async()=>{
 const browser=await chromium.launch({channel:'chrome',headless:true});
 const report={url,cases:[],errors:[],screenshots:[]};
 try{
 const context=await browser.newContext({viewport:{width:1440,height:900},deviceScaleFactor:1}),page=await context.newPage();
 page.on('pageerror',e=>report.errors.push(String(e)));
 const state=()=>page.evaluate(()=>cubeOrderLab.getState());
 const load=async text=>{await page.locator('#algorithm').fill(text);await page.locator('#algorithmForm button[type=submit]').click();await page.waitForFunction(()=>!cubeOrderLab.getState().dirty);};
 const waitIdle=()=>page.waitForFunction(()=>!cubeOrderLab.getState().busy&&!cubeOrderLab.getState().playing,null,{timeout:20000});
 const solved=s=>s.state.every((v,i)=>v===i);
 await page.goto(url);await page.waitForFunction(()=>window.cubeOrderLab);await page.evaluate(()=>document.fonts.ready);
 assert.equal((await state()).order,'6');
 for(const [n,order] of [[2,'15'],[3,'105'],[4,'420'],[5,'420']]){
  await page.locator('#cubeSize').selectOption(String(n));await load('R U');const s=await state();assert.equal(s.size,n);assert.equal(s.order,order);assert.equal(await page.locator('#order').textContent(),order);assert(solved(s));
  await page.locator('#atIdentity').click();const at=await state();assert.equal(at.repeats,order);assert(solved(at));
  await page.locator('#beforeIdentity').click();assert(!solved(await state()));
  report.cases.push({case:`${n} cube R U exact order`,order});
 }
 await page.locator('#cubeSize').selectOption('3');await load('[R,U]');await page.locator('#speed').selectOption('0');await page.locator('#play').click();await waitIdle();let s=await state();assert.equal(s.repeats,'6');assert(solved(s));report.cases.push({case:'[R,U] automatically stops at its sixth repetition',state:{order:s.order,repeats:s.repeats,step:s.step}});
 const large='900719925474099312345';await page.locator('#exponent').fill(large);await page.locator('#jumpForm button[type=submit]').click();const largeState=await state();assert.equal(largeState.repeats,large);await page.locator('#exponent').fill(String(BigInt(large)%6n));await page.locator('#jumpForm button[type=submit]').click();assert.deepEqual((await state()).state,largeState.state);report.cases.push({case:'Arbitrary repetition jump stays exact beyond Number precision'});
 await page.locator('#reset').click();await page.locator('#next').click();await waitIdle();assert.equal((await state()).step,1);await page.locator('#previous').click();assert(solved(await state()));
 await page.locator('#speed').selectOption('650');await page.locator('#play').click();await page.waitForTimeout(150);await page.locator('#play').click();s=await state();assert(!s.busy&&!s.playing);await page.waitForTimeout(750);assert.deepEqual((await state()).state,s.state);await page.locator('#reset').click();assert(solved(await state()));report.cases.push({case:'Step/back, pause in mid-turn, and reset preserve exact state'});
 await page.locator('#cubeSize').selectOption('5');await page.locator('#speed').selectOption('0');await page.locator('#layerMode').selectOption('single');await page.locator('#layerValue').selectOption('3');assert.equal(await page.locator('[data-face=R]').textContent(),'3R');await page.locator('[data-face=R]').click();await waitIdle();s=await state();assert.equal(s.moves[0].depth,3);assert.equal(s.moves[0].width,1);assert.equal(s.order,'4');
 await page.locator('#layerMode').selectOption('wide');await page.locator('#layerValue').selectOption('3');assert.equal(await page.locator('[data-face=U]').textContent(),'3Uw');await page.locator('[data-face=U]').click();await waitIdle();s=await state();assert.equal(s.moves.at(-1).width,3);assert.equal(s.moves.at(-1).depth,1);assert.equal(s.moves.length,2);report.cases.push({case:'Fifth-order inner and wide buttons record correct selected layers',moves:s.moves});
 // High-layer notation becomes invalid on a smaller cube; a clean valid load must recover.
 await load('5R');await page.locator('#cubeSize').selectOption('2');assert((await state()).dirty);assert.equal(await page.locator('#order').textContent(),'—');await load('R');assert.equal((await state()).order,'4');
 await page.locator('#fullscreen').click();await page.waitForFunction(()=>Boolean(document.fullscreenElement));await page.locator('#cubeSize').selectOption('4');assert.equal((await state()).size,4);await page.locator('#layerMode').selectOption('single');await page.locator('#layerValue').selectOption('2');await page.locator('[data-face=F]').click();await waitIdle();assert.equal((await state()).moves.at(-1).depth,2);await page.locator('#fullscreen').click();await page.waitForFunction(()=>!document.fullscreenElement);report.cases.push({case:'Fullscreen selectors and face buttons keep correct hit positions'});
 await page.locator('#cubeSize').selectOption('5');await load('R U');await page.locator('#reset').click();await page.locator('.console').evaluate(e=>e.scrollTop=0);await page.screenshot({path:path.join(output,'rubik-order-desktop.png')});report.screenshots.push(path.join(output,'rubik-order-desktop.png'));
 const bounds=await page.evaluate(()=>({scroll:document.documentElement.scrollWidth,viewport:innerWidth,canvas:document.getElementById('cube').getBoundingClientRect().toJSON()}));assert(bounds.scroll<=bounds.viewport);assert(bounds.canvas.width>300&&bounds.canvas.height>300);
 await page.setViewportSize({width:390,height:844});await page.locator('#cubeSize').selectOption('3');await load('[R,U]');await page.evaluate(()=>scrollTo(0,0));await page.screenshot({path:path.join(output,'rubik-order-mobile.png'),fullPage:true});report.screenshots.push(path.join(output,'rubik-order-mobile.png'));const mobile=await page.evaluate(()=>({width:innerWidth,scroll:document.documentElement.scrollWidth}));assert(mobile.scroll<=mobile.width);
 await page.locator('#speed').selectOption('0');await page.locator('#play').click();await waitIdle();assert.equal((await state()).repeats,'6');assert(solved(await state()));report.cases.push({case:'Mobile width has no horizontal overflow and complete repeat playback works'});
 assert.deepEqual(report.errors,[]);report.passed=true;await context.close();
 }catch(error){report.failure=String(error.stack||error);process.exitCode=1;}finally{fs.writeFileSync(path.join(output,'rubik-order-browser-qa.json'),JSON.stringify(report,null,2));console.log(JSON.stringify(report,null,2));await browser.close();}
})();
