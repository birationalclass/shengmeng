/* Fixed-height lecture pages. CSS columns preserve text and live controls. */
(()=>{
  'use strict';
  const $=id=>document.getElementById(id),body=document.body,scene=$('scene');
  const mobile=matchMedia('(max-width:1000px)');
  body.classList.add('screen-deck');body.dataset.screenMode='notes';
  const toolbar=document.createElement('div');toolbar.className='screen-toolbar';
  const topics=$('chapter-nav');
  topics.after(toolbar);toolbar.append(topics);
  const modes=document.createElement('div');modes.className='screen-modes';
  modes.setAttribute('role','group');modes.setAttribute('aria-label','课件内容');
  modes.innerHTML='<button type="button" data-screen-mode="notes" aria-pressed="true">概念</button><button type="button" data-screen-mode="experiment" aria-pressed="false">互动</button>';
  $('workspace').append(modes);
  const copy=document.querySelector('.lesson-copy'),notes=document.createElement('section');
  notes.className='screen-pane';notes.setAttribute('aria-label','概念与讲解');
  copy.before(notes);notes.innerHTML='<h3 class="screen-pane-title">概念与讲解</h3>';
  const reference=document.querySelector('.reference');reference.open=true;copy.append(reference);
  reference.querySelector('summary').tabIndex=-1;
  reference.querySelector('summary').addEventListener('click',e=>e.preventDefault());
  function pane(container,flow,name){
    const window=document.createElement('div');window.className='screen-window';
    const pager=document.createElement('div');pager.className='screen-pager';
    pager.innerHTML=`<button type="button" aria-label="${name}上一页">←</button><span aria-live="polite"></span><button type="button" aria-label="${name}下一页">→</button>`;
    flow.classList.add('screen-flow');container.append(window);window.append(flow);container.append(pager);
    const state={flow,window,pager,index:0,total:1,name};
    pager.firstElementChild.onclick=()=>turn(state,-1);pager.lastElementChild.onclick=()=>turn(state,1);
    return state;
  }
  const a=pane(notes,copy,'概念'),b=pane(document.querySelector('.experiment'),scene,'互动'),panes=[a,b];
  let scheduled=false,sceneId='',pendingTarget=null;
  const tabState=new WeakMap();
  function update(state){
    if(!state.window.clientWidth||!state.window.clientHeight)return;
    const width=state.flow.clientWidth,gap=parseFloat(getComputedStyle(state.flow).columnGap)||28;
    state.total=Math.max(1,Math.round((state.flow.scrollWidth+gap)/(width+gap)));
    state.index=Math.min(state.index,state.total-1);
    state.flow.dataset.pages=state.total;
    state.flow.style.transform=`translateX(${-state.index*(width+gap)}px)`;
    const label=`${window.CourseLanguage?.language==='en'?(state.name==='概念'?'Concepts':'Explore'):state.name} ${state.index+1} / ${state.total}`;
    if(state.pager.querySelector('span').textContent!==label)state.pager.querySelector('span').textContent=label;
    state.pager.firstElementChild.disabled=state.index===0;state.pager.lastElementChild.disabled=state.index===state.total-1;
    const box=state.window.getBoundingClientRect();
    state.flow.querySelectorAll('button,a,input,select,summary').forEach(el=>{
      if(!tabState.has(el))tabState.set(el,el.getAttribute('tabindex'));
      const r=el.getBoundingClientRect(),visible=r.width>0&&r.right>box.left+1&&r.left<box.right-1;
      if(visible){const old=tabState.get(el);old===null?el.removeAttribute('tabindex'):el.setAttribute('tabindex',old);}else el.tabIndex=-1;
    });
  }
  function turn(state,delta){state.index=Math.max(0,Math.min(state.total-1,state.index+delta));update(state);}
  function mode(value){body.dataset.screenMode=value;modes.querySelectorAll('[data-screen-mode]').forEach(button=>button.setAttribute('aria-pressed',String(button.dataset.screenMode===value)));queue();}
  function refresh(){
    scheduled=false;
    if(sceneId!==scene.dataset.lessonScene){sceneId=scene.dataset.lessonScene;panes.forEach(p=>p.index=0);pendingTarget=null;}
    scene.querySelectorAll('details').forEach(details=>{details.open=true;const summary=details.querySelector('summary');if(summary&&!summary.dataset.screenStatic){summary.dataset.screenStatic='true';summary.tabIndex=-1;summary.addEventListener('click',event=>event.preventDefault());}});
    panes.forEach(update);
    if(pendingTarget){
      const target=scene.querySelector(pendingTarget);pendingTarget=null;
      if(target&&b.window.clientWidth){const width=b.flow.clientWidth,gap=parseFloat(getComputedStyle(b.flow).columnGap)||28,rect=target.getBoundingClientRect(),base=b.flow.getBoundingClientRect();b.index=Math.max(0,Math.min(b.total-1,Math.floor((rect.left-base.left+1)/(width+gap))));update(b);}
    }
  }
  function queue(){if(!scheduled){scheduled=true;requestAnimationFrame(refresh);}}
  modes.querySelectorAll('[data-screen-mode]').forEach(button=>button.onclick=()=>mode(button.dataset.screenMode));
  scene.addEventListener('click',e=>{
    if(e.target.closest('[data-criterion],[data-proof]')){b.index=0;queue();}
    if(e.target.closest('#criteria-next,#criteria-back')){pendingTarget='#criteria-proof';queue();}
    if(e.target.closest('#proof-next,#proof-back')){pendingTarget='#proof-board';queue();}
    if(e.target.closest('[data-answer]')){pendingTarget='.quiz-feedback';queue();}
    if(e.target.closest('#quiz-next,#quiz-retry')){b.index=0;queue();}
    if(e.target.closest('#exercise-proof-next')){pendingTarget='.exercise-proof';queue();}
  });
  const observer=new MutationObserver(records=>{
    if(records.some(record=>!record.target.closest?.('svg,#relation-graph,#quotient-graph,#symmetry-graph,#symmetry-second')))queue();
  });
  observer.observe(scene,{childList:true,subtree:true,characterData:true});
  observer.observe(copy,{childList:true,subtree:true,characterData:true});
  observer.observe($('chapter-nav'),{subtree:true,attributes:true,attributeFilter:['aria-current']});
  new ResizeObserver(queue).observe($('workspace'));
  window.addEventListener('resize',queue);window.visualViewport?.addEventListener('resize',queue);
  mobile.addEventListener('change',queue);document.fonts?.ready.then(queue);
  window.LessonScreen={step(delta){turn(mobile.matches&&body.dataset.screenMode==='notes'?a:b,delta);},refresh:queue};
  queue();
})();
