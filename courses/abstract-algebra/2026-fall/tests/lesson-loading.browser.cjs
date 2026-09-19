const {chromium}=require('playwright');
const assert=require('node:assert/strict');
(async()=>{
 const browser=await chromium.launch({headless:true,channel:'chrome',args:['--enable-webgl','--enable-unsafe-swiftshader']});
 const page=await browser.newPage();const errors=[],requests=[];page.on('pageerror',e=>errors.push(e.message));page.on('request',r=>requests.push(r.url()));
 const base=process.env.COURSE_TEST_URL||'http://127.0.0.1:8768/courses/abstract-algebra/2026-fall/';
 await page.goto(base+'?view=lesson&section=2.5#burnside');
 let frame=await page.locator('#lecture-frame').contentFrame();
 await frame.locator('.notebook-entry').first().waitFor();
 await frame.locator('html.lesson-loading').waitFor({state:'detached'});
 let f=page.frames().find(f=>f.url().includes('/lesson-groups/'));
 assert.deepEqual(await f.evaluate(()=>Object.keys(GroupCourseContent)),['2.5']);
 console.log('initial anchor',await f.evaluate(()=>location.hash));
 assert(!requests.some(u=>/\/sections\/(?!2\.5\.json)/.test(u)),requests.join('\n'));
 assert(!requests.some(u=>/\/(content|chapter-two|textbook-references|exercises)\.js/.test(u)));
 assert(!requests.some(u=>/\/(opening|opening-galois-portrait|opening-lettering-data)\.js/.test(u)));
 assert(!requests.some(u=>/\/lesson-1\/\?/.test(u)));
 assert.equal(await page.locator('#lecture-frame').count(),1);
 console.log('only current section loaded; opening bundle absent');
 await page.locator('#portal-next').click();assert(f.isDetached());
 await page.frameLocator('#lecture-frame').locator('.notebook-entry').first().waitFor();
 f=page.frames().find(f=>f.url().includes('/lesson-groups/'));assert.deepEqual(await f.evaluate(()=>Object.keys(GroupCourseContent)),['2.6']);
 await page.locator('#portal-course-open').click();assert(f.isDetached());assert.equal(await page.locator('#lecture-frame').count(),0);console.log('old contexts destroyed on section change and exit');
 await page.goBack();await page.frameLocator('#lecture-frame').locator('.notebook-entry').first().waitFor();assert.match(page.url(),/section=2.6/);
 for(const id of ['1.2','1.1']){
  await page.goto(base+'?view=lesson&section='+id+'#check');
  await page.frameLocator('#lecture-frame').locator('.notebook-entry').first().waitFor();
  f=page.frames().find(f=>f.url().includes('/lesson-1/'));
  assert.deepEqual(await f.evaluate(()=>Object.keys(LessonNotebookContent)),[id]);
  assert.deepEqual(await f.evaluate(()=>Object.keys(TextbookExercises.banks)),[id]);
  console.log('first lesson data isolated',id);
 }
 // Switch away while a lesson's payload is deliberately delayed.
 await page.route('**/sections/2.4.json*',async route=>{await new Promise(r=>setTimeout(r,1200));try{await route.continue();}catch{}});
 await page.goto(base+'?view=lesson&section=2.4');await page.locator('#portal-next').click();
 await page.frameLocator('#lecture-frame').locator('.notebook-entry').first().waitFor();assert.match(page.url(),/section=2.5/);assert.equal(await page.locator('#lecture-frame').count(),1);
 console.log('rapid navigation preserves latest section');
 assert.deepEqual(errors,[]);await browser.close();
})().catch(e=>{console.error(e);process.exit(1)});
