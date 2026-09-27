/* Fetch only the requested section. The parent owns this document's lifetime. */
(()=>{
  'use strict';
  const version='20260927-loading-v2';
  const first=location.pathname.includes('/lesson-1/');
  const requested=new URLSearchParams(location.search).get('section');
  const valid=first?/^1\.[12]$/:/^(1\.[3-7]|2\.[1-7]|3\.[1-6]|4\.[1-5])$/;
  const id=valid.test(requested)?requested:first?'1.1':'1.3';
  const controller=new AbortController();
  let disposed=false;
  const notify=(type,extra={})=>{if(parent!==window)parent.postMessage({type,section:id,...extra},location.origin);};
  const progress=(percent,zh,en)=>{window.CourseLoad?.update(percent,zh,en);notify('lesson-progress',{percent,zh,en});};
  const bounded=promise=>new Promise((resolve,reject)=>{const timer=setTimeout(()=>reject(Error('Loading timeout')),45000);promise.then(value=>{clearTimeout(timer);resolve(value);},error=>{clearTimeout(timer);reject(error);});});
  document.documentElement.classList.add('lesson-loading');
  // Start ahead of shared renderers, without downloading any other section.
  const data=fetch(`sections/${id}.json?v=${version}`,{signal:controller.signal,priority:'high'}).then(response=>{
    if(!response.ok)throw new Error(`Section ${id}: HTTP ${response.status}`);
    return response.json();
  });
  data.catch(()=>{}); // The DOM/deferred dependencies may finish after the request.
  window.addEventListener('pagehide',()=>{disposed=true;controller.abort();},{once:true});
  window.addEventListener('message',event=>{
    if(event.origin!==location.origin||event.source!==parent)return;
    if(event.data?.type==='course-navigate'&&event.data.section===id&&/^[a-z-]+$/.test(event.data.anchor))location.hash=event.data.anchor;
    if(event.data?.type==='course-language')window.CourseLanguage?.set(event.data.language);
  });
  function script(src){return new Promise((resolve,reject)=>{
    if(disposed){reject(new DOMException('Lesson closed','AbortError'));return;}
    const node=document.createElement('script');node.src=src;
    const timer=setTimeout(()=>{node.remove();reject(Error(`Timeout loading ${src}`));},45000);
    node.onload=()=>{clearTimeout(timer);resolve();};node.onerror=()=>{clearTimeout(timer);reject(new Error(`Unable to load ${src}`));};
    document.head.append(node);
  });}
  async function start(){
    try{
      progress(12,`§${id} · 正在加载内容与样式`,`§${id} · Loading content and styles`);
      const [payload]=await bounded(Promise.all([data,window.CourseLoad.stylesReady()]));if(disposed)return;
      let scripts;
      if(first){
        window.LessonNotebookContent={[id]:payload.notebook};
        window.CurrentLessonExercises={[id]:payload.exercises};
        scripts=[...(id==='1.2'?['axiom-lab.js','associativity-sudoku.js']:[]),'exercises-runtime.js','lesson.js','screen.js','embedded.js','../lesson-keyboard.js'];
      }else{
        window.GroupCourseContent={[id]:payload.book};
        window.GroupCourseExercises={[id]:payload.exercises};
        window.GroupTextbookReferences={[id]:payload.references};
        scripts=[...(id==='1.4'?['symmetric-difference.js']:[]),...(Number(id[0])>=3?['ring-models.js','ring-visuals.js']:['models.js','visuals.js']),'lesson.js','../lesson-1/screen.js','../lesson-1/embedded.js','../lesson-keyboard.js'];
      }
      for(const [i,src] of scripts.entries()){
        progress(25+Math.round(i/scripts.length*60),`§${id} · 正在准备交互 ${i+1}/${scripts.length}`,`§${id} · Preparing interactions ${i+1}/${scripts.length}`);
        await script(`${src}?v=${version}`);
      }
      if(disposed)return;
      if(!window.LessonScreen||!document.querySelector('.notebook-entry'))throw Error('Lesson renderer did not initialize');
      document.documentElement.classList.remove('lesson-loading');
      await new Promise(resolve=>requestAnimationFrame(resolve));
      if(disposed)return;
      window.CourseLoad.finish();notify('lesson-ready');
      window.dispatchEvent(new Event('lesson-ready'));
    }catch(error){
      if(disposed||error.name==='AbortError')return;
      console.error('Lesson loading failed:',error);
      window.CourseLoad.fail();notify('lesson-error');
    }
  }
  if(document.readyState==='loading')document.addEventListener('DOMContentLoaded',start,{once:true});else start();
})();
