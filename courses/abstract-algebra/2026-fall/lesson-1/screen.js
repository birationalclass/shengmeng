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
  function cards(){
    const current=entries[selected];
    notebook.innerHTML=`<div class="notebook-heading"><span>§ ${book.id}</span><h2>${en()?book.titleEn:book.title}</h2></div><div class="notebook-entries">${entries.map((e,i)=>`<article class="notebook-entry ${i===selected?'is-current':''}" data-entry="${i}"><button class="notebook-entry-heading" type="button" data-notebook-entry="${i}" aria-expanded="${i===selected}" aria-current="${i===selected?'step':'false'}" aria-controls="notebook-entry-${i}"><span><small>${text(e.ref)}</small><strong>${text(e.title)}</strong></span><span class="notebook-fold" aria-hidden="true">${i===selected?'−':'+'}</span></button>${i!==selected&&e.formula?`<div class="notebook-preview" aria-hidden="true">${formula(e).split('<br>')[0]}</div>`:''}<div class="notebook-entry-body" id="notebook-entry-${i}" ${i===selected?'':'hidden'}>${e.formula?`<div class="notebook-formula">${formula(e)}</div>`:''}<p>${text(e.text)}</p></div></article>`).join('')}</div>`;
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
    footer.setAttribute('aria-label',en()?'Lesson progress':'讲义进度');
    scene.querySelector('.notebook-exposition')?.setAttribute('aria-label',en()?'Mathematical explanation':'数学阐述');
    const e=entries[selected];
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
