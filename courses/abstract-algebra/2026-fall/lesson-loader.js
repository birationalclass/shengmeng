/* Fetch only the requested section. The parent owns this document's lifetime. */
(()=>{
  'use strict';
  const version='20260927-card-magic-v1';
  const first=location.pathname.includes('/lesson-1/');
  const requested=new URLSearchParams(location.search).get('section');
  const valid=first?/^1\.[12]$/:/^(1\.[3-7]|2\.[1-7]|3\.[1-6]|4\.[1-5])$/;
  const id=valid.test(requested)?requested:first?'1.1':'1.3';
  const health=window.CourseHealth;
  let stage='data',resource=`${id}.json`;
  const controller=new AbortController();
  let disposed=false;
  const notify=(type,extra={})=>{if(parent!==window)parent.postMessage({type,section:id,...extra},location.origin);};
  const progress=(percent,zh,en)=>{window.CourseLoad?.update(percent,zh,en);notify('lesson-progress',{percent,zh,en});};
  const bounded=promise=>new Promise((resolve,reject)=>{const timer=setTimeout(()=>reject(Error('Loading timeout')),45000);promise.then(value=>{clearTimeout(timer);resolve(value);},error=>{clearTimeout(timer);reject(error);});});
  document.documentElement.classList.add('lesson-loading');
  // Start ahead of shared renderers, without downloading any other section.
  const data=fetch(`sections/${id}.json?v=${version}`,{signal:controller.signal,priority:'high'}).then(response=>{
    if(!response.ok)throw Object.assign(new Error(`Section ${id}: HTTP ${response.status}`),{healthStatus:response.status});
    return response.json();
  });
  data.catch(error=>{if(error.name==='AbortError')return;const status=error.healthStatus?` (HTTP ${error.healthStatus})`:'';health?.report('D-DATA',`§${id} 小节数据读取失败${status}；请刷新或拍照反馈。`,`Section ${id} data failed${status}. Reload or share a photo.`,{key:'lesson-data'});});
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
      health?.clear('lesson-data');stage='script';
      let scripts;
      if(first){
        window.LessonNotebookContent={[id]:payload.notebook};
        window.CurrentLessonExercises={[id]:payload.exercises};
        scripts=[...(id==='1.2'?['axiom-lab.js','associativity-sudoku.js']:[]),'exercises-runtime.js','lesson.js','screen.js','embedded.js','../lesson-keyboard.js'];
      }else{
        window.GroupCourseContent={[id]:payload.book};
        window.GroupCourseExercises={[id]:payload.exercises};
        window.GroupTextbookReferences={[id]:payload.references};
        scripts=[...(id==='1.4'?['symmetric-difference.js']:id==='1.6'?['card-magic.js']:[]),...(Number(id[0])>=3?['ring-models.js','ring-visuals.js']:['models.js','visuals.js']),'lesson.js','../lesson-1/screen.js','../lesson-1/embedded.js','../lesson-keyboard.js'];
      }
      for(const [i,src] of scripts.entries()){
        resource=src.split('/').pop();
        progress(25+Math.round(i/scripts.length*60),`§${id} · 正在准备交互 ${i+1}/${scripts.length}`,`§${id} · Preparing interactions ${i+1}/${scripts.length}`);
        await script(`${src}?v=${version}`);
      }
      if(disposed)return;
      stage='render';
      if(!window.LessonScreen||!document.querySelector('.notebook-entry'))throw Error('Lesson renderer did not initialize');
      document.documentElement.classList.remove('lesson-loading');
      await new Promise(resolve=>requestAnimationFrame(resolve));
      if(disposed)return;
      window.CourseLoad.finish();notify('lesson-ready');
      health?.clear('lesson-load');health?.appReady();
      window.dispatchEvent(new Event('lesson-ready'));
    }catch(error){
      if(disposed||error.name==='AbortError')return;
      console.error('Lesson loading failed:',error);
      health?.ready('app');
      const label=stage==='data'?'内容或样式':stage==='script'?`脚本 ${resource}`:'正文初始化';
      const english=stage==='data'?'content or styles':stage==='script'?`script ${resource}`:'lesson initialization';
      health?.report('D-LESSON',`§${id} ${label}未完成；请刷新或拍照反馈。`,`Section ${id}: ${english} failed. Reload or share a photo.`,{key:'lesson-load'});
      window.CourseLoad.fail();notify('lesson-error');
    }
  }
  if(document.readyState==='loading')document.addEventListener('DOMContentLoaded',start,{once:true});else start();
})();
