(()=>{
  if(window.parent===window)return;
  document.body.classList.add('embedded-lesson');
  const notify=()=>window.parent.postMessage({type:'lesson-location',section:new URLSearchParams(location.search).get('section'),anchor:location.hash.slice(1)},location.origin);
  document.addEventListener('click',event=>{const a=event.target.closest('a');if(!a)return;const url=new URL(a.href,location.href);if(url.origin!==location.origin)return;
    if(a.dataset.textbookSection){event.preventDefault();window.parent.postMessage({type:'course-route',view:'lesson',section:a.dataset.textbookSection,anchor:url.hash.slice(1)},location.origin);}
    else if(a.classList.contains('back')||a.closest('footer')||a.classList.contains('brand')){event.preventDefault();window.parent.postMessage({type:'course-route',view:'course'},location.origin);}
  });
  window.addEventListener('message',event=>{if(event.origin!==location.origin||event.source!==window.parent)return;
    const data=event.data;if(data?.type==='course-language')window.CourseLanguage?.set(data.language);
    if(data?.type==='course-navigate'&&data.section===new URLSearchParams(location.search).get('section')&&/^[a-z-]+$/.test(data.anchor))location.hash=data.anchor;
  });
  window.addEventListener('lesson-rendered',notify);window.addEventListener('hashchange',notify);notify();window.LessonScreen?.refresh();
})();
