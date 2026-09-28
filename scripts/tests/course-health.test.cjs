const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path');
const {JSDOM}=require('jsdom'),acorn=require('acorn');
const source=fs.readFileSync(path.resolve(__dirname,'../../assets/course-health.js'),'utf8');
const wait=ms=>new Promise(resolve=>setTimeout(resolve,ms));
async function create(mode='index',html='',change=()=>{}){
 const dom=new JSDOM('<!doctype html><html lang="zh-CN"><body>'+html+'</body></html>',{url:'https://course.test/course/',runScripts:'outside-only',pretendToBeVisual:true});
 const w=dom.window;w.CSS={supports:()=>true};w.fetch=()=>Promise.resolve();w.ResizeObserver=function(){};w.structuredClone=structuredClone;
 w.HTMLDialogElement.prototype.showModal=function(){this.open=true;};
 Object.defineProperty(w.HTMLScriptElement.prototype,'noModule',{value:false,configurable:true});
 Object.defineProperty(w.document,'currentScript',{value:{getAttribute:()=>mode},configurable:true});
 change(w);w.eval(source);await wait(10);return dom;
}
test('diagnostic bootstrap parses as ES5 and never sends network or telemetry requests',()=>{
 acorn.parse(source,{ecmaVersion:5});assert.doesNotMatch(source,/\bfetch\s*\(|sendBeacon|XMLHttpRequest|\.preventDefault\s*\(/);
});
test('healthy page is quiet; messages deduplicate, translate and clear',async()=>{
 const dom=await create();try{const w=dom.window,h=w.CourseHealth;assert.equal(w.document.querySelector('#course-health-notice'),null);
 h.report('D-TEST','测试错误','Test error');h.report('D-TEST','测试错误','Test error');assert.equal(h.snapshot().length,1);
 const note=w.document.querySelector('#course-health-notice');assert.match(note.textContent,/测试错误/);assert.equal(note.style.pointerEvents,'none');
 w.document.documentElement.lang='en';await wait(5);assert.match(note.textContent,/Test error/);
 h.clear('D-TEST');assert.equal(note.style.display,'none');
 }finally{dom.window.close();}
});
test('missing capabilities and unavailable storage are explicit, not fake network errors',async()=>{
 const dom=await create('sudoku','',w=>{w.fetch=undefined;w.structuredClone=undefined;Object.defineProperty(w,'localStorage',{get(){throw Error('denied')}})});
 try{const issues=dom.window.CourseHealth.snapshot();assert(issues.some(x=>x.code==='D-COMPAT'&&x.en.includes('fetch')));assert(issues.some(x=>x.code==='D-STORAGE'));}finally{dom.window.close();}
});
test('resource and runtime errors expose only basename, not URL tokens or error payloads',async()=>{
 const dom=await create();try{const w=dom.window,script=w.document.createElement('script');script.src='/assets/lesson.js?token=PRIVATE';w.document.body.append(script);script.dispatchEvent(new w.Event('error'));
 w.dispatchEvent(new w.ErrorEvent('error',{filename:'https://course.test/app.js?student=PRIVATE',lineno:8,error:new w.TypeError('PRIVATE secret'),message:'PRIVATE secret'}));
 const text=JSON.stringify(w.CourseHealth.snapshot());assert.match(text,/lesson.js/);assert.match(text,/app.js:8/);assert.doesNotMatch(text,/PRIVATE|token=|student=/);
 }finally{dom.window.close();}
});
test('watchdog detects silent startup and can recover',async()=>{
 const dom=await create();try{const h=dom.window.CourseHealth;h.expect('x','课件','Lesson',15);await wait(30);assert.equal(h.snapshot()[0].code,'D-WAIT');h.ready('x');assert.equal(h.snapshot().length,0);}finally{dom.window.close();}
});
test('notice follows modal and fullscreen surface without stealing focus',async()=>{
 const dom=await create('index','<button id="focus">button</button><dialog id="dialog"></dialog><section id="full"></section>');
 try{const w=dom.window,d=w.document;d.getElementById('focus').focus();w.CourseHealth.report('D-TEST','测试','Test');const note=d.getElementById('course-health-notice');
 d.getElementById('dialog').open=true;await wait(5);assert.equal(note.parentNode.id,'dialog');assert.equal(d.activeElement.id,'focus');
 d.getElementById('dialog').open=false;Object.defineProperty(d,'fullscreenElement',{value:d.getElementById('full'),configurable:true});d.dispatchEvent(new w.Event('fullscreenchange'));assert.equal(note.parentNode.id,'full');
 }finally{dom.window.close();}
});
test('only current same-origin lesson frames can report; removing one clears its errors',async()=>{
 const dom=await create('index','<iframe id="lesson"></iframe>');try{const w=dom.window,frame=w.document.getElementById('lesson');const send=(origin='https://course.test',source=frame.contentWindow)=>w.dispatchEvent(new w.MessageEvent('message',{origin,source,data:{type:'course-health',action:'report',entry:{key:'test',code:'D-TEST',zh:'子页面','en':'Child',severity:'error'}}}));
 send('https://other.test');send('https://course.test',w);assert.equal(w.CourseHealth.snapshot().length,0);send();assert.equal(w.CourseHealth.snapshot().length,1);
 const old=frame.contentWindow;frame.remove();w.CourseHealth.refresh();send('https://course.test',old);assert.equal(w.CourseHealth.snapshot().length,0);
 }finally{dom.window.close();}
});
test('scroll checks are passive, avoid boundaries, detect repeated stuck input and clear on motion',async()=>{
 const dom=await create('index','<div id="course-scroll-region" style="overflow:auto">text</div>');try{const w=dom.window,el=w.document.getElementById('course-scroll-region');let height=200;
 el.getClientRects=()=>[{height,width:600}];Object.defineProperties(el,{clientHeight:{get:()=>height},scrollHeight:{get:()=>1000}});
 w.CourseHealth.checkScroll();assert.equal(w.CourseHealth.snapshot().length,0);
 for(let i=0;i<3;i++){const e=new w.WheelEvent('wheel',{deltaY:-100,bubbles:true,cancelable:true});el.dispatchEvent(e);assert.equal(e.defaultPrevented,false);await wait(460);}assert.equal(w.CourseHealth.snapshot().length,0,'top boundary is normal');
 for(let i=0;i<3;i++){const e=new w.WheelEvent('wheel',{deltaY:100,bubbles:true,cancelable:true});el.dispatchEvent(e);assert.equal(e.defaultPrevented,false);await wait(460);}assert(w.CourseHealth.snapshot().some(x=>x.code==='D-SCROLL'));
 el.scrollTop=80;el.dispatchEvent(new w.Event('scroll'));assert.equal(w.CourseHealth.snapshot().length,0);
 height=10;w.CourseHealth.checkScroll();assert(w.CourseHealth.snapshot().some(x=>x.code==='D-SCROLL'));height=200;w.CourseHealth.checkScroll();assert.equal(w.CourseHealth.snapshot().length,0);
 }finally{dom.window.close();}
});
test('offline warning clears after online signal without claiming server recovery',async()=>{
 const dom=await create();try{const w=dom.window;Object.defineProperty(w.navigator,'onLine',{value:false,configurable:true});w.dispatchEvent(new w.Event('offline'));w.CourseHealth.report('D-SERVER','服务器未连接','Server not connected',{severity:'warning'});
 Object.defineProperty(w.navigator,'onLine',{value:true});w.dispatchEvent(new w.Event('online'));assert.equal(w.CourseHealth.snapshot().length,1);assert.equal(w.CourseHealth.snapshot()[0].code,'D-SERVER');
 }finally{dom.window.close();}
});

test('all entry points carry an ES5 fallback that remains visible in a modal',async()=>{
 const root=path.resolve(__dirname,'../..');
 const pages=['courses/abstract-algebra/index.html','courses/abstract-algebra/2026-fall/index.html','courses/abstract-algebra/2026-fall/lesson-1/index.html','courses/abstract-algebra/2026-fall/lesson-groups/index.html','courses/abstract-algebra/generators/index.html','courses/abstract-algebra/card-magic/index.html','courses/abstract-algebra/rubik/index.html','visuals/group-sudoku/index.html'];
 for(const page of pages){
  const html=fs.readFileSync(path.join(root,page),'utf8');
  const doc=new JSDOM(html);const script=doc.window.document.querySelector('script[data-health-page]');assert(script,page);
  const fallback=script.getAttribute('onerror');acorn.parse(fallback,{ecmaVersion:5});assert.match(html,/D-NOSCRIPT/);doc.window.close();
  const dom=new JSDOM('<html><body><dialog id="modal"></dialog></body></html>',{runScripts:'outside-only'});
  try{const w=dom.window;w.eval(fallback);await wait(5);const note=w.document.querySelector('[role=status]');assert.match(note.textContent,/D-MONITOR/);w.document.getElementById('modal').open=true;await wait(5);assert.equal(note.parentNode.id,'modal');}finally{dom.window.close();}
 }
});
