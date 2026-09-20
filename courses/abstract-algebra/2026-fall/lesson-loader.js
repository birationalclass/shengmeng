/* Fetch only the requested section. The parent owns this document's lifetime. */
(()=>{
  'use strict';
  const version='20260920-multiplication-game-v4';
  const first=location.pathname.includes('/lesson-1/');
  const requested=new URLSearchParams(location.search).get('section');
  const valid=first?/^1\.[12]$/:/^(1\.[3-7]|2\.[1-7]|3\.[1-6]|4\.[1-5])$/;
  const id=valid.test(requested)?requested:first?'1.1':'1.3';
  const controller=new AbortController();
  let disposed=false;
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
    node.onload=resolve;node.onerror=()=>reject(new Error(`Unable to load ${src}`));
    document.head.append(node);
  });}
  async function start(){
    const en=()=>window.CourseLanguage?.language==='en';
    const status=document.createElement('div');status.className='lesson-load-status';status.setAttribute('role','status');
    const label=document.createElement('p');label.textContent=`§${id} · ${en()?'Loading lesson':'正在加载课件'}`;
    status.append(label);document.body.append(status);
    try{
      const payload=await data;if(disposed)return;
      let scripts;
      if(first){
        window.LessonNotebookContent={[id]:payload.notebook};
        window.CurrentLessonExercises={[id]:payload.exercises};
        scripts=[...(id==='1.2'?['axiom-lab.js','associativity-sudoku.js']:[]),'exercises-runtime.js','lesson.js','screen.js','embedded.js','../lesson-keyboard.js'];
      }else{
        window.GroupCourseContent={[id]:payload.book};
        window.GroupCourseExercises={[id]:payload.exercises};
        window.GroupTextbookReferences={[id]:payload.references};
        scripts=[...(Number(id[0])>=3?['ring-models.js','ring-visuals.js']:['models.js','visuals.js']),'lesson.js','../lesson-1/screen.js','../lesson-1/embedded.js','../lesson-keyboard.js'];
      }
      for(const src of scripts)await script(`${src}?v=${version}`);
      if(disposed)return;
      document.documentElement.classList.remove('lesson-loading');status.remove();
      window.dispatchEvent(new Event('lesson-ready'));
    }catch(error){
      if(disposed||error.name==='AbortError')return;
      console.error('Lesson loading failed:',error);
      label.textContent=`§${id} · ${en()?'Could not load lesson':'课件加载未完成'}`;
      const retry=document.createElement('button');retry.type='button';retry.textContent=en()?'Retry':'重新加载';retry.onclick=()=>location.reload();status.append(retry);
    }
  }
  document.addEventListener('DOMContentLoaded',start,{once:true});
})();
