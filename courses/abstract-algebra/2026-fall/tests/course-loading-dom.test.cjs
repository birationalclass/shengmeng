const {JSDOM,ResourceLoader,VirtualConsole,fs,assert,repo,prefix,wait,Loader,shims,lesson}=require('./course-dom-harness.cjs');
async function scenario(fault){
 let release;const gate=new Promise(r=>release=r);const errors=[];
 class Faults extends Loader{fetch(url,opts){if(url.includes('/lesson-1/lesson.css')){if(fault==='slow')return gate.then(()=>super.fetch(url,opts));if(fault==='css')return Promise.reject(Error('offline css'));}if(fault==='script'&&url.includes('/lesson-groups/models.js'))return Promise.reject(Error('offline script'));return super.fetch(url,opts)}}
 const vc=new VirtualConsole();vc.on('jsdomError',e=>{if(e.type!=='css parsing')errors.push(e.message)});
 const dom=new JSDOM(fs.readFileSync(repo+prefix+'lesson-groups/index.html','utf8'),{url:'http://course.test'+prefix+'lesson-groups/?embedded=1&section=1.4#set-group-construction',runScripts:'dangerously',resources:new Faults(),pretendToBeVisual:true,beforeParse:shims,virtualConsole:vc});
 const d=dom.window.document;
 if(fault==='slow'){await wait(70);assert.equal(d.querySelector('#course-load-cover').hidden,false);assert(d.querySelector('[data-load-label]').textContent);assert.equal(d.querySelector('.notebook-entry'),null);release();}
 for(let i=0;i<80;i++){await wait(30);if(d.querySelector('#course-load-cover').hidden||d.querySelector('#course-load-cover').dataset.failed)break;}
 if(fault==='slow'){assert.equal(d.querySelector('#course-load-cover').hidden,true);assert(errors.every(e=>e.startsWith('Could not parse CSS')));}
 else{assert.equal(d.querySelector('#course-load-cover').hidden,false);assert.equal(d.querySelector('#course-load-cover').dataset.failed,'true');assert.match(d.querySelector('[data-load-label]').textContent,/重试/);let retried=false;dom.window.CourseLoad.retry=()=>{retried=true};d.querySelector('#course-load-cover button').click();assert(retried);}
 console.log('loading scenario:',fault,'passed');
}
async function portal(){
 class ParentLoader extends Loader{fetch(url,opts){if(opts.element?.localName==='iframe')return Promise.resolve(Buffer.from('<!doctype html><body>Lesson</body>'));return super.fetch(url,opts)}}
 const vc=new VirtualConsole(),errors=[];vc.on('jsdomError',e=>{if(e.type!=='css parsing')errors.push(e.message)});
 const dom=new JSDOM(fs.readFileSync(repo+prefix+'index.html','utf8'),{url:'http://course.test'+prefix+'?view=lesson&section=1.4#set-group-construction',runScripts:'dangerously',resources:new ParentLoader(),pretendToBeVisual:true,beforeParse:shims,virtualConsole:vc});
 await wait(300);const w=dom.window,d=w.document,frame=d.querySelector('#lecture-frame');assert(frame,errors.join('\n'));assert.equal(frame.style.visibility,'hidden');assert.equal(d.querySelector('#course-load-cover').hidden,false);
 const msg=(f,type,section='1.4')=>w.dispatchEvent(new w.MessageEvent('message',{origin:w.location.origin,source:f.contentWindow,data:{type,section}}));
 msg(frame,'lesson-ready');await wait(70);assert.equal(d.querySelector('#course-load-cover').hidden,true);assert.equal(frame.style.visibility,'');
 d.querySelector('#portal-next').click();const next=d.querySelector('#lecture-frame');assert.notEqual(next,frame);assert.equal(next.style.visibility,'hidden');assert.equal(d.querySelector('#course-load-cover').hidden,false);msg(frame,'lesson-ready');await wait(50);assert.equal(d.querySelector('#course-load-cover').hidden,false,'stale iframe cannot reveal new lesson');msg(next,'lesson-ready','1.5');await wait(70);assert.equal(d.querySelector('#course-load-cover').hidden,true);
 d.querySelector('#portal-course-open').click();await wait(70);assert.equal(d.querySelector('#lecture-frame'),null);assert.equal(d.querySelector('#course-load-cover').hidden,true);
 console.log('portal lifecycle passed; DOM limitations/errors:',errors);assert.deepEqual(errors,[]);
}
(async()=>{for(const id of ['1.1','1.2','1.4','1.6','2.5','3.1'])await lesson(id);await scenario('slow');await scenario('css');await scenario('script');await portal();process.exit(0)})().catch(e=>{console.error(e);process.exit(1)});
