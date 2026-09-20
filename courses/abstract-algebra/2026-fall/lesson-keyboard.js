/* Enter and Space belong to lesson progression, never the focused button. */
(()=>{
  'use strict';
  const held=new Set();
  const lesson=()=>document.body.classList.contains('screen-deck');
  const active=()=>lesson()||document.body.classList.contains('portal-lesson');
  const blocked=()=>!!document.querySelector('dialog[open]');
  const key=e=>e.key==='Enter'?'Enter':e.key===' '||e.key==='Spacebar'?'Space':null;
  const gameActive=()=>!!(document.querySelector('.algebra-sudoku')||document.querySelector('#lecture-frame')?.contentDocument?.querySelector('.algebra-sudoku'));
  const editing=target=>gameActive()||target?.closest?.('.algebra-sudoku,textarea,select,input:not([type="button"]):not([type="submit"]):not([type="reset"]):not([type="checkbox"]):not([type="radio"]),[contenteditable]:not([contenteditable="false"])');
  function advance(){
    if(!active()||blocked())return;
    if(lesson())window.LessonScreen?.advance();
    else{
      const frame=document.getElementById('lecture-frame');
      if(frame&&!frame.hidden)frame.contentWindow?.postMessage({type:'lesson-advance'},location.origin);
    }
  }
  window.addEventListener('keydown',e=>{
    const name=key(e);
    if(!name||!active()||e.isComposing||e.keyCode===229||e.altKey||e.ctrlKey||e.metaKey||e.shiftKey||editing(e.target))return;
    e.preventDefault();e.stopImmediatePropagation();
    if(e.repeat||held.has(name))return;
    held.add(name);advance();
  },true);
  window.addEventListener('keyup',e=>{
    const name=key(e);if(!name)return;
    const consumed=held.delete(name);
    if(consumed||(active()&&!editing(e.target)&&!e.isComposing&&!e.altKey&&!e.ctrlKey&&!e.metaKey&&!e.shiftKey)){
      e.preventDefault();e.stopImmediatePropagation();
    }
  },true);
  window.addEventListener('blur',()=>held.clear());
  window.addEventListener('message',e=>{
    if(window.parent!==window&&e.source===window.parent&&e.origin===location.origin&&e.data?.type==='lesson-advance')advance();
  });
})();
