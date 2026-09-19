const {chromium}=require('playwright'),assert=require('node:assert/strict');
(async()=>{
 const browser=await chromium.launch({channel:'chrome',headless:true});const p=await browser.newPage(),errors=[],bad=[],requests=[];
 p.on('pageerror',e=>errors.push(e.message));p.on('request',r=>requests.push(r.url()));
 const base=process.env.COURSE_TEST_URL||'http://127.0.0.1:8768/courses/abstract-algebra/2026-fall/';
 const sections=['3.1','3.2','3.3','3.4','3.5','3.6','4.1','4.2','4.3','4.4','4.5'];
 const settle=()=>p.evaluate(()=>new Promise(r=>requestAnimationFrame(()=>requestAnimationFrame(r))));let cards=0,controls=0,exercises=0;
 for(const width of [1280,390]){
  await p.setViewportSize({width,height:width===390?844:1000});
  for(const lang of ['zh','en'])for(const section of sections){
   await p.goto(base+`lesson-groups/?embedded=1&section=${section}&lang=${lang}`);
   await p.locator('.notebook-entry').first().waitFor();await p.locator('html.lesson-loading').waitFor({state:'detached'});
   assert.deepEqual(await p.evaluate(()=>Object.keys(GroupCourseContent)),[section]);
   const entries=await p.evaluate(()=>GroupCourseContent[LessonBook.id].entries.map(e=>({id:e.id,visual:e.visual,proof:e.proof?.length||0})));
   for(const entry of entries){
    await p.evaluate(id=>LessonBook.navigate(id),entry.id);await settle();
    const problems=await p.evaluate(()=>({overflow:document.documentElement.scrollWidth>innerWidth+1,formula:[...document.querySelectorAll('.notebook-entry.is-current .katex-display,#scene .katex-display')].filter(e=>e.clientWidth&&(e.scrollWidth>e.clientWidth+3||parseFloat(getComputedStyle(e).fontSize)<12)).map(e=>({text:e.querySelector('annotation')?.textContent,font:getComputedStyle(e).fontSize,width:e.clientWidth,scroll:e.scrollWidth}))}));
    if(problems.overflow||problems.formula.length){const issue={section,entry:entry.id,width,lang,...problems};bad.push(issue);console.log('LAYOUT',JSON.stringify(issue));}
    assert.equal(await p.locator('.katex-error').count(),0);assert(!/^§\d/.test((await p.locator('.notebook-entry.is-current .notebook-reference').innerText()).trim()));
    if(width===1280&&lang==='zh'&&entry.proof){for(let i=0;i<entry.proof;i++)await p.locator('#proof-next').evaluate(el=>el.click());assert.equal(await p.locator('.group-proof-step').count(),entry.proof);}
    if(width===1280&&entry.visual){
     const selectIds=await p.locator('.ring-lab select').evaluateAll(nodes=>nodes.map(n=>n.id));
     for(const id of selectIds){const values=await p.locator('#'+id).locator('option').evaluateAll(nodes=>nodes.map(n=>n.value));for(const value of values){await p.locator('#'+id).selectOption(value);controls++;}}
     for(const selector of ['#euclid-all','#division-next','#frac-equivalent','#quot-representative','#char-add'])if(await p.locator(selector).count()){await p.locator(selector).evaluate(el=>{if(!el.disabled)el.click();});controls++;}
    }
    if(width===1280&&lang==='zh'&&((section==='4.4'&&entry.id==='gaussian-division')||(section==='4.5'&&entry.id==='gauss')))await p.screenshot({path:`/private/tmp/rings-${entry.id}.png`});
    cards++;
   }
   if(width===1280){
    await p.evaluate(()=>{localStorage.removeItem(`algebra-groups-v1-${LessonBook.id}`);});
    // Reload resets the in-memory saved-answer map as well as storage.
    await p.goto(base+`lesson-groups/?embedded=1&section=${section}&lang=${lang}#check`);await p.reload();await p.locator('.quiz-question').waitFor();
    const answers=await p.evaluate(()=>GroupCourseExercises[LessonBook.id].map(q=>q.written?null:q.answer));
    for(let i=0;i<answers.length;i++){if(answers[i]===null){await p.locator('#written-answer').fill('My proof outline');await p.locator('#written-reveal').click();assert((await p.locator('.quiz-feedback').innerText()).length>40);}else{await p.locator(`[data-answer="${answers[i]}"]`).click();assert.match(await p.locator('.quiz-feedback').innerText(),lang==='zh'?/正确/:/Correct/);await p.locator('#quiz-next').click();}exercises++;}
   }
  }
  console.log('Rendered width',width);
 }
 // Entry directly into chapter four fetches its data and ring models only.
 requests.length=0;await p.goto(base+'?view=lesson&section=4.4#euclid-algorithm');await p.frameLocator('#lecture-frame').locator('.ring-lab').waitFor();
 let frame=p.frames().find(f=>f.url().includes('/lesson-groups/'));assert.deepEqual(await frame.evaluate(()=>Object.keys(GroupCourseContent)),['4.4']);
 assert(!requests.some(u=>/\/sections\/(?!4\.4\.json)/.test(u)));assert(!requests.some(u=>/\/(content|chapter-(two|three|four)|ring-exercises|opening|models|visuals)\.js/.test(u)));
 await p.locator('#portal-next').click();assert(frame.isDetached());await p.frameLocator('#lecture-frame').locator('.ring-lab').waitFor();frame=p.frames().find(f=>f.url().includes('/lesson-groups/'));assert.equal(await frame.evaluate(()=>LessonBook.id),'4.5');
 await p.locator('#portal-course-open').click();assert(frame.isDetached());assert.equal(await p.locator('#lecture-frame').count(),0);
 console.log(JSON.stringify({cards,controls,exercises,errors,bad},null,2));await browser.close();assert.deepEqual(errors,[]);assert.deepEqual(bad,[]);
})().catch(e=>{console.error(e);process.exit(1)});
