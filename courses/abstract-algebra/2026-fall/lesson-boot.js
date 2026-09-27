/* Inlined before external dependencies so loading feedback never needs a fetch. */
(()=>{
 const box=document.getElementById('course-load-cover'),label=box.querySelector('[data-load-label]'),bar=box.querySelector('[role="progressbar"]'),value=box.querySelector('[data-load-value]'),retry=box.querySelector('button');
 const lang=()=>(window.CourseLanguage?.language||new URLSearchParams(location.search).get('lang'))==='en';
 let slow,deadline,ticket=0,active=true;
 const text=(zh,en)=>lang()?en:zh;
 function update(percent,zh,en){if(!active)return;label.textContent=text(zh,en);bar.setAttribute('aria-valuenow',String(percent));value.textContent=percent+'%';box.style.setProperty('--load-progress',percent+'%');}
 function show(){active=true;ticket++;delete box.dataset.failed;box.hidden=false;document.documentElement.classList.add('course-load-active');clearTimeout(deadline);deadline=setTimeout(fail,90000);clearTimeout(slow);slow=setTimeout(()=>{if(active)label.textContent=text('连接较慢，正在继续加载；也可重试。','Still loading on a slow connection. You can retry.');},20000);update(0,'正在准备课件','Preparing lesson');retry.textContent=text('重新加载','Reload');}
 function finish(){const current=++ticket;update(100,'课件已就绪','Lesson ready');clearTimeout(slow);clearTimeout(deadline);requestAnimationFrame(()=>requestAnimationFrame(()=>{if(current!==ticket)return;active=false;box.hidden=true;document.documentElement.classList.remove('course-load-active');}));}
 function fail(){clearTimeout(slow);clearTimeout(deadline);label.textContent=text('加载未完成，请重试。','Loading did not finish. Please retry.');box.dataset.failed='true';}
 function stylesReady(){return Promise.all(Array.from(document.querySelectorAll('link[data-course-style]'),link=>new Promise((resolve,reject)=>{if(link.dataset.loadState==='error')return reject(Error('Stylesheet unavailable'));if(link.sheet||link.dataset.loadState==='ready')return resolve();link.addEventListener('load',resolve,{once:true});link.addEventListener('error',()=>reject(Error('Stylesheet unavailable')),{once:true});})));}
 const api=window.CourseLoad={update,show,finish,fail,stylesReady,retry:()=>location.reload()};retry.onclick=()=>api.retry();show();
 window.addEventListener('pagehide',()=>{active=false;clearTimeout(slow);clearTimeout(deadline);ticket++;});
 window.addEventListener('pageshow',event=>{if(event.persisted&&document.documentElement.classList.contains('lesson-loading'))location.reload();});
})();
