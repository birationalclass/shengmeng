/* A textbook notebook paired with its live mathematical demonstration. */
(()=>{
  'use strict';
  const $=id=>document.getElementById(id),body=document.body,scene=$('scene'),book=window.LessonBook;
  if(!book||!window.LessonNotebookContent)return;
  const entries=window.LessonNotebookContent[book.id],workspace=$('workspace'),experiment=scene.parentElement;
  const en=()=>window.CourseLanguage?.language==='en',text=pair=>pair[en()?1:0];
  const reader=()=>matchMedia('(max-width:760px)').matches?workspace:experiment;
  const resetScroll=()=>{
    experiment.scrollTop=0;workspace.scrollTop=0;
    if(matchMedia('(max-width:760px)').matches&&scene.dataset.lessonScene==='check')workspace.scrollTop=Math.max(0,experiment.getBoundingClientRect().top-workspace.getBoundingClientRect().top);
  };
  body.classList.add('screen-deck','notebook-deck');
  document.querySelector('.lesson-copy').hidden=true;$('chapter-nav').hidden=true;
  const reference=document.querySelector('.reference');if(reference)document.querySelector('.lesson-copy').append(reference);
  experiment.removeAttribute('aria-labelledby');
  const notebook=document.createElement('aside');notebook.className='lesson-notebook';notebook.setAttribute('aria-label','教材讲义');
  workspace.prepend(notebook);
  const footer=document.createElement('nav');footer.className='notebook-navigation';footer.setAttribute('aria-label','讲义进度');
  footer.innerHTML='<button type="button" id="notebook-back"></button><div class="notebook-location"><span id="notebook-position"></span><small id="notebook-key-hint"></small></div><button type="button" id="notebook-next"></button>';
  document.querySelector('main').append(footer);
  let selected=Math.max(0,entries.findIndex(x=>x.topic===scene.dataset.lessonScene)),selecting=false,scheduled=false;
  const formula=e=>en()&&e.formulaEn?e.formulaEn:e.formula;
  const bookIcon='<svg class="notebook-book-icon" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M12 5.5C9 3.6 5.5 3.5 2.5 4.5v14c3-1 6.5-.9 9.5 1 3-1.9 6.5-2 9.5-1v-14c-3-1-6.5-.9-9.5 1Z"/><path d="M12 5.5v14"/></svg>';
  const extensionIcon='<svg class="notebook-book-icon notebook-extension-icon" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 5V4a3 3 0 0 1 6 0v1h4a1 1 0 0 1 1 1v4h-1a3 3 0 0 0 0 6h1v4a1 1 0 0 1-1 1h-4v-1a3 3 0 0 0-6 0v1H5a1 1 0 0 1-1-1v-4H3a3 3 0 0 1 0-6h1V6a1 1 0 0 1 1-1Z"/></svg>';
  const quizIcon='<svg class="notebook-book-icon" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="4" y="3" width="16" height="18" rx="2"/><path d="m8 9 2 2 5-5M8 16h8"/></svg>';
  const rail=document.createElement('nav');rail.className='notebook-reading-rail';
  const railTrack=document.createElement('div');railTrack.className='notebook-rail-track';rail.append(railTrack);workspace.append(rail);
  let railHover=-1,railFrame=0;
  function syncRail(){
    rail.setAttribute('aria-label',en()?'Reading outline':'阅读导航');
    railTrack.innerHTML=entries.map((e,i)=>`<button type="button" class="notebook-rail-mark" data-rail-entry="${i}" aria-label="${en()?'Reading outline':'阅读导航'} · ${text(e.ref)} ${text(e.title)}"><span class="notebook-rail-tick" aria-hidden="true"></span><span class="notebook-rail-caption" aria-hidden="true">${text(e.ref)} · ${text(e.title)}</span></button>`).join('');
    queueRail();
  }
  function paintRail(){
    railFrame=0;
    const mobile=matchMedia('(max-width:760px)').matches,pane=mobile?workspace:notebook,box=pane.getBoundingClientRect();
    const top=Math.max(0,box.top)+12,bottom=Math.min(innerHeight,box.bottom)-12,height=Math.min(400,Math.max(0,bottom-top));
    rail.style.left=Math.max(4,box.left-40)+'px';rail.style.top=(top+Math.max(0,(bottom-top-height)/2))+'px';rail.style.height=height+'px';
    rail.hidden=height<48;
    let current=selected;
    if(!mobile){
      const line=box.top+box.height*.22;let distance=Infinity;
      notebook.querySelectorAll('.notebook-entry').forEach((entry,i)=>{const r=entry.getBoundingClientRect(),d=line<r.top?r.top-line:line>r.bottom?line-r.bottom:0;if(d<distance){current=i;distance=d;}});
    }
    railTrack.querySelectorAll('button').forEach((button,i)=>{
      const d=Math.abs(i-(railHover>=0?railHover:current));button.style.setProperty('--rail-tick-width',(d===0?27:d===1?20:d===2?14:8)+'px');
      if(i===current)button.setAttribute('aria-current','location');else button.removeAttribute('aria-current');
      button.classList.toggle('is-selected',i===selected);
    });
  }
  function queueRail(){if(!railFrame)railFrame=requestAnimationFrame(paintRail);}
  railTrack.addEventListener('click',event=>{const button=event.target.closest('[data-rail-entry]');if(button)select(+button.dataset.railEntry);});
  railTrack.addEventListener('pointermove',event=>{const button=event.target.closest('[data-rail-entry]'),i=button?+button.dataset.railEntry:-1;if(i!==railHover){railHover=i;queueRail();}});
  rail.addEventListener('pointerleave',()=>{railHover=-1;queueRail();});
  rail.addEventListener('wheel',event=>{
    if(event.ctrlKey||!event.deltaY)return;event.preventDefault();
    const pane=matchMedia('(max-width:760px)').matches?workspace:notebook,unit=event.deltaMode===1?16:event.deltaMode===2?pane.clientHeight:1;
    pane.scrollTop+=event.deltaY*unit;
  },{passive:false});
  notebook.addEventListener('scroll',queueRail,{passive:true});workspace.addEventListener('scroll',queueRail,{passive:true});
  window.addEventListener('resize',queueRail);document.addEventListener('fullscreenchange',queueRail);
  function cards(){
    const current=entries[selected];
    notebook.innerHTML=`<div class="notebook-heading"></div><div class="notebook-entries">${entries.map((e,i)=>`
      <article class="notebook-entry ${i===selected?'is-current':''}" data-entry="${i}" data-extension="${!!e.extension}">
        <button class="notebook-entry-heading" type="button" data-notebook-entry="${i}" aria-expanded="${i===selected}" aria-current="${i===selected?'step':'false'}" aria-controls="notebook-entry-${i}">
          <span class="notebook-entry-label"><span class="notebook-reference">${e.topic==='check'?quizIcon:e.extension?extensionIcon:bookIcon}<span>${text(e.ref)}</span></span><strong>${text(e.title)}</strong></span><span class="notebook-fold" aria-hidden="true">${i===selected?'−':'+'}</span>
        </button>
        ${i!==selected&&e.formula?`<div class="notebook-preview" aria-hidden="true">${formula(e).split('<br>')[0]}</div>`:''}
        <div class="notebook-entry-body" id="notebook-entry-${i}" ${i===selected?'':'hidden'}>
          ${e.extension?`<div class="notebook-extension-label">${en()?'Extension · beyond the textbook':'扩展 · 非教材条目'}</div>`:''}
          ${e.formula?`<div class="notebook-formula">${formula(e)}</div>`:''}<p>${text(e.text)}</p>${e.detail?`<p>${text(e.detail)}</p>`:''}${e.groupSudoku?`<p class="group-sudoku-entry"><a href="../../../../visuals/group-sudoku/" target="_blank" rel="noopener">${en()?'Group Sudoku · 3D adventure ↗':'群数独 · 三维闯关 ↗'}</a></p>`:''}
        </div>
      </article>`).join('')}</div>`;
    notebook.setAttribute('aria-label',en()?'Textbook notebook':'教材讲义');
    notebook.dataset.topic=current.topic;
    const picker=document.createElement('select');picker.className='notebook-mobile-index';picker.setAttribute('aria-label',en()?'Lesson entry':'本节条目');
    picker.innerHTML=entries.map((e,i)=>`<option value="${i}" ${i===selected?'selected':''}>${text(e.ref)} · ${text(e.title)}</option>`).join('');
    notebook.querySelector('.notebook-heading').append(picker);
    experiment.setAttribute('aria-label',text(current.title));
    experiment.dataset.notebookTopic=current.topic;
    if(current.topic!=='check')document.querySelector('.quiz-status')?.remove();
    const top=notebook.querySelector('.is-current');
    if(top){const r=top.getBoundingClientRect(),p=notebook.getBoundingClientRect();if(r.bottom>p.bottom||r.top<p.top)notebook.scrollTop+=r.top-p.top-16;}
    syncRail();
  }
  function splitScene(){
    if(!scene.firstElementChild||scene.firstElementChild.classList.contains('notebook-visual'))return;
    const children=[...scene.children],visual=document.createElement('div'),exposition=document.createElement('section');
    visual.className='notebook-visual';exposition.className='notebook-exposition';
    exposition.setAttribute('aria-label',en()?'Mathematical explanation':'数学阐述');
    scene.append(visual,exposition);
    for(const node of children){
      const explanation=node.matches('.mini-proof,#operation-proof,#power-track,#table-readout,#example-note,#status,#criteria-note,.quiz-feedback,.exercise-proof,.insight:not(#partition-relation)');
      (explanation?exposition:visual).append(node);
    }
    // Quiz navigation follows the reasoning; all existing event handlers stay on
    // their original nodes. Mathematical models and answers are unchanged.
    const quiz=visual.querySelector('#quiz-next');if(quiz)exposition.append(quiz.closest('.controls'));
    const details=exposition.querySelector('.mini-proof');if(details)details.open=true;
    if(!exposition.children.length)exposition.hidden=true;
  }
  function labels(){
    const e=entries[selected],proof=scene.querySelector('#proof-next,#criteria-next,#exercise-proof-next');
    const proofPending=proof&&!proof.disabled&&proof.dataset.proofComplete!=='true';
    const quiz=scene.querySelector('#quiz-next');
    const scroller=reader(),unread=scroller.scrollTop+scroller.clientHeight<scroller.scrollHeight-8;
    const waiting=quiz?.disabled&&!unread;
    const last=selected===entries.length-1&&!proofPending&&!unread&&!quiz;
    const values={
      'notebook-back':en()?'← Previous':'← 上一条',
      'notebook-position':text(e.ref)+' · '+text(e.title),
      'notebook-key-hint':en()?'Enter / Space to continue':'回车 / 空格继续',
      'notebook-next':waiting?(en()?'Choose an answer':'请先选择答案'):last?(en()?'Section complete':'本节完成'):proofPending?(en()?'Continue proof →':'继续证明 →'):(en()?'Continue →':'继续 →')
    };
    for(const [id,value] of Object.entries(values))if($(id).textContent!==value)$(id).textContent=value;
    $('notebook-back').disabled=selected===0&&scroller.scrollTop<2;
    $('notebook-next').disabled=!!waiting||last;
  }
  function refresh(){
    scheduled=false;splitScene();
    queueRail();
    footer.setAttribute('aria-label',en()?'Lesson progress':'讲义进度');
    scene.querySelector('.notebook-exposition')?.setAttribute('aria-label',en()?'Mathematical explanation':'数学阐述');
    const e=entries[selected];
    scene.classList.toggle('relation-as-function',e.topic==='relation'&&!!e.extension);
    let functionNote=scene.querySelector('.notebook-function-note');
    if(e.topic==='relation'&&e.extension){
      if(!functionNote){functionNote=document.createElement('div');functionNote.className='notebook-function-note';scene.querySelector('.relation-layout')?.before(functionNote);}
      const hint=en()?'Click 0 or 1 to change the value of R for the row and column pair. F = False, T = True.':'点击矩阵中的 0 或 1，改变 R 对这一对元素的取值。F = False，T = True。';
      if(functionNote.textContent!==hint)functionNote.textContent=hint;
    }else functionNote?.remove();
    // The statement is kept on the left throughout the proof. The right panel
    // starts with its central equation and then becomes the step-by-step proof.
    let focus=scene.querySelector('.notebook-focus-formula');
    if(e.proof!==undefined||e.criterion!==undefined){
      if(!focus){focus=document.createElement('div');focus.className='notebook-focus-formula';scene.querySelector('.notebook-visual')?.prepend(focus);}
      const markup=`<div>${formula(e)}</div><p>${en()?'Continue to unfold the proof.':'继续，逐步展开证明。'}</p>`;
      const version=selected+':'+en();
      if(focus.dataset.version!==version){focus.innerHTML=markup;focus.dataset.version=version;}
      const board=scene.querySelector('#proof-board,#criteria-proof');
      focus.hidden=!!board?.querySelector('.expression,.criteria-step');
    }else focus?.remove();
    labels();
    const options=scene.querySelector('.quiz-options');
    if(options){
      const buttons=[...options.querySelectorAll('button')],ctx=document.createElement('canvas').getContext('2d');
      const widths=buttons.map(button=>{const style=getComputedStyle(button);ctx.font=style.font;return ctx.measureText(button.textContent).width+parseFloat(style.paddingLeft)+parseFloat(style.paddingRight)+2;});
      const width=options.clientWidth,gap=14;
      options.dataset.columns=widths.reduce((a,b)=>a+b,0)+gap*(buttons.length-1)<=width?'4':Math.max(...widths)>width*.8?'1':'2';
    }
  }
  function queue(){if(!scheduled){scheduled=true;requestAnimationFrame(refresh);}}
  function select(index){
    if(index<0||index>=entries.length)return;
    selected=index;selecting=true;const e=entries[index];
    if(scene.dataset.lessonScene!==e.topic)book.navigate(e.topic);
    splitScene();
    if(e.proof!==undefined)scene.querySelector(`[data-proof="${e.proof}"]`)?.click();
    if(e.criterion!==undefined)scene.querySelector(`[data-criterion="${e.criterion}"]`)?.click();
    selecting=false;cards();resetScroll();refresh();
    if(e.exposition){const detail=scene.querySelector('.notebook-exposition');if(detail)reader().scrollTop+=detail.getBoundingClientRect().top-reader().getBoundingClientRect().top-24;}
  }
  function scroll(delta){
    const scroller=reader(),before=scroller.scrollTop;
    scroller.scrollTop=Math.max(0,Math.min(scroller.scrollHeight-scroller.clientHeight,before+delta*Math.max(120,scroller.clientHeight*.72)));
    return Math.abs(scroller.scrollTop-before)>2;
  }
  function advance(){
    refresh();
    const proof=scene.querySelector('#proof-next,#criteria-next,#exercise-proof-next');
    if(proof&&!proof.disabled&&proof.dataset.proofComplete!=='true'){
      const board=scene.querySelector('#proof-board,#criteria-proof,.exercise-proof');
      const r=board?.getBoundingClientRect(),p=reader().getBoundingClientRect();
      if(r&&r.height>0&&(r.top>=p.bottom||r.bottom<=p.top)){if(scroll(1)){labels();return;}}
      proof.click();queue();return;
    }
    if(scroll(1)){labels();return;}
    const quiz=scene.querySelector('#quiz-next');
    if(quiz){if(!quiz.disabled){quiz.click();resetScroll();queue();}return;}
    select(selected+1);
  }
  function back(){
    const proof=scene.querySelector('#proof-back,#criteria-back');
    if(proof&&!proof.disabled){proof.click();queue();return;}
    if(scroll(-1)){labels();return;}
    select(selected-1);
  }
  notebook.addEventListener('click',event=>{
    const button=event.target.closest('[data-notebook-entry]');if(!button)return;
    const i=+button.dataset.notebookEntry;
    if(i!==selected){select(i);return;}
    const content=$('notebook-entry-'+i),open=content.hidden;content.hidden=!open;button.setAttribute('aria-expanded',String(open));button.querySelector('.notebook-fold').textContent=open?'−':'+';
    queueRail();
  });
  notebook.addEventListener('change',event=>{if(event.target.matches('.notebook-mobile-index'))select(+event.target.value);});
  $('notebook-next').onclick=advance;$('notebook-back').onclick=back;
  experiment.addEventListener('scroll',labels,{passive:true});
  workspace.addEventListener('scroll',labels,{passive:true});
  scene.addEventListener('click',event=>{
    if(event.target.closest('[data-answer]'))requestAnimationFrame(()=>{splitScene();const feedback=scene.querySelector('.quiz-feedback');if(feedback)reader().scrollTop+=feedback.getBoundingClientRect().top-reader().getBoundingClientRect().top-24;queue();});
    if(event.target.closest('#quiz-next,#quiz-prev,#quiz-retry')){resetScroll();queue();}
  });
  window.addEventListener('lesson-rendered',()=>{
    if(selecting)return;
    selected=Math.max(0,entries.findIndex(x=>x.topic===scene.dataset.lessonScene));
    if(scene.dataset.lessonScene!=='check')document.querySelector('.quiz-status')?.remove();
    cards();resetScroll();refresh();
  });
  new MutationObserver(records=>{
    if(records.some(r=>!r.target.closest?.('svg,#relation-graph,#quotient-graph,#symmetry-graph,#symmetry-second')))queue();
  }).observe(scene,{childList:true,subtree:true,characterData:true});
  new ResizeObserver(queue).observe(workspace);
  window.addEventListener('course-language',()=>{cards();queue();});
  window.addEventListener('lesson-quiz-jump',()=>{resetScroll();queue();});
  document.fonts?.ready.then(queue);
  window.LessonScreen={advance,step:delta=>delta>0?advance():back(),refresh:queue};
  cards();refresh();
})();
