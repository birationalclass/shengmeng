(()=>{
'use strict';
const $=id=>document.getElementById(id),en=()=>window.CourseLanguage.language==='en',t=pair=>Array.isArray(pair)?pair[en()?1:0]:pair;
const html=pair=>window.GroupLessonMath.inline(t(pair));
const id=new URLSearchParams(location.search).get('section')||'1.3',book=window.GroupCourseContent[id];
if(!book){$('scene').textContent='未找到这一小节。Section not found.';return;}
const formula=tex=>{
 if(!tex)return '';
 const lines=tex.split(/[,;]?\\(?:qquad|quad)\s*/);
 const display=lines.length>1?String.raw`\begin{gathered}`+lines.join(String.raw`\\{} `)+String.raw`\end{gathered}`:tex;
 return window.katex.renderToString(display,{displayMode:true,throwOnError:true,strict:'ignore',output:'htmlAndMathml'});
};
function fitMath(){
 document.querySelectorAll('.katex-display').forEach(display=>{
  if(!display.clientWidth)return;
  const base=Number(display.dataset.baseFont)||parseFloat(getComputedStyle(display).fontSize);
  display.dataset.baseFont=base;display.style.fontSize=base+'px';
  const math=display.querySelector('.katex-html');if(!math)return;
  const width=Math.max(display.scrollWidth,math.scrollWidth,math.getBoundingClientRect().width),available=display.clientWidth-8;
  if(width>available&&available>0)display.style.fontSize=(base*available/width)+'px';
 });
}
window.addEventListener('lesson-rendered',()=>requestAnimationFrame(fitMath));
window.addEventListener('course-language',()=>requestAnimationFrame(fitMath));
window.addEventListener('resize',()=>requestAnimationFrame(fitMath));
document.fonts?.ready.then(()=>requestAnimationFrame(fitMath));
const reference=e=>window.GroupTextbookReferences[id][e.id];
const entries=book.entries.concat({id:'check',title:['自测与书面练习','Self-check and written exercise'],tex:'',text:['本节原创练习。先独立作答，再查看理由；最后完成一道书面证明。答案与进度保存在当前浏览器中。','Original exercises for this section. Answer independently, then review the reasoning and finish a written proof. Progress is stored in this browser.']});
window.LessonNotebookContent={[id]:entries.map(e=>({topic:e.id,ref:e.id==='check'?['本节自测','Section self-check']:reference(e).label,title:e.title,formula:formula(e.tex),text:e.text.map(window.GroupLessonMath.inline),detail:book.optional?['拓展阅读 · 不增加既定课表中的必讲课时。','Optional reading · outside the required scheduled teaching.']:undefined}))};
let current=0,quizIndex=0;
const key=`algebra-groups-v1-${id}`;let saved={};try{saved=JSON.parse(localStorage.getItem(key)||'{}');}catch{}
const save=()=>{try{localStorage.setItem(key,JSON.stringify(saved));}catch{}};
function proofPanel(root,steps){
let step=0;
root.innerHTML='<div class="group-proof-statement"></div><div id="proof-board" class="group-proof-board" aria-live="polite"></div><div class="controls"><button id="proof-back" type="button"></button><button id="proof-next" type="button" class="primary"></button><span class="group-proof-progress"></span></div>';
const draw=()=>{root.querySelector('#proof-board').innerHTML=step?steps.slice(0,step).map((s,i)=>`<article class="group-proof-step"><span>${String(i+1).padStart(2,'0')}</span><p>${html(s)}</p></article>`).join(''):`<p class="hint">${t(['先阅读左侧完整命题，再开始证明。','Read the complete statement on the left, then begin the proof.'])}</p>`;const back=root.querySelector('#proof-back'),next=root.querySelector('#proof-next');back.textContent=t(['← 上一步','← Previous step']);back.disabled=step===0;next.textContent=step===0?t(['开始证明 →','Begin proof →']):step===steps.length?t(['证明完成','Proof complete']):t(['继续证明 →','Continue proof →']);next.disabled=step===steps.length;next.dataset.proofComplete=String(step===steps.length);root.querySelector('.group-proof-progress').textContent=`${step} / ${steps.length}`;window.LessonScreen?.refresh();};
root.querySelector('#proof-back').onclick=()=>{step=Math.max(0,step-1);draw();};root.querySelector('#proof-next').onclick=()=>{step=Math.min(steps.length,step+1);draw();};draw();
}
function quiz(root){
const questions=window.GroupCourseExercises[id],q=questions[quizIndex],answer=saved[quizIndex];
root.innerHTML=`<div class="notebook-visual"><div class="quiz-progress">${t(['本节自测','Section self-check'])} · ${quizIndex+1} / ${questions.length}</div><h3 class="quiz-question">${html(q.question)}</h3>${q.written?`<label class="written-label">${t(['先写下你的证明思路','Write your proof outline first'])}<textarea id="written-answer" rows="5" placeholder="${t(['关键步骤与所用定理…','Key steps and theorems…'])}"></textarea></label><button id="written-reveal" type="button">${t(['对照参考证明','Compare with the proof'])}</button>`:`<div class="quiz-options">${q.options.map((o,i)=>`<button type="button" data-answer="${i}" ${answer!==undefined?'disabled':''} class="${answer!==undefined?(i===q.answer?'correct':i===answer?'incorrect':''):''}"><span>${String.fromCharCode(65+i)}.</span> ${html(o)}</button>`).join('')}</div>`}</div><section class="notebook-exposition"><div class="quiz-feedback" aria-live="polite">${q.written?saved['reveal'+quizIndex]?html(q.reason):'':answer!==undefined?`<b>${t(answer===q.answer?['正确','Correct']:['再想一想','Reconsider'])}</b>${html(q.reason)}`:''}</div><div class="controls"><button id="quiz-prev" type="button" ${quizIndex===0?'disabled':''}>${t(['上一题','Previous question'])}</button><button id="quiz-retry" type="button">${t(['重做本题','Retry'])}</button><button id="${quizIndex===questions.length-1?'quiz-finish':'quiz-next'}" type="button" ${quizIndex===questions.length-1||(!q.written&&answer===undefined)?'disabled':''}>${quizIndex===questions.length-1?t(['本节完成','Section complete']):t(['下一题 →','Next question →'])}</button></div><small>${t(['本节练习为依照教材主题设计的原创题，不使用教材习题编号。','These are original questions aligned with the section, not numbered textbook exercises.'])}</small></section>`;
root.querySelectorAll('[data-answer]').forEach(b=>b.onclick=()=>{saved[quizIndex]=+b.dataset.answer;save();quiz(root);});
root.querySelector('#quiz-prev').onclick=()=>{quizIndex--;quiz(root);};root.querySelector('#quiz-next')?.addEventListener('click',()=>{if(quizIndex<questions.length-1){quizIndex++;quiz(root);}});
root.querySelector('#quiz-retry').onclick=()=>{delete saved[quizIndex];delete saved['reveal'+quizIndex];save();quiz(root);};
if(q.written){const input=root.querySelector('#written-answer');input.value=saved['text'+quizIndex]||'';input.oninput=()=>{saved['text'+quizIndex]=input.value;save();};root.querySelector('#written-reveal').onclick=()=>{saved['reveal'+quizIndex]=true;save();quiz(root);};}
window.LessonScreen?.refresh();
}
function show(i){
if(i<0||i>=entries.length)return;current=i;const e=entries[i],scene=$('scene');
$('section-title').textContent=t(e.title);$('experiment-label').textContent=`${e.id==='check'?t(['本节自测','Section self-check']):t(reference(e).label)} · ${t(e.title)}`;$('intro-title').textContent=t(book.title);document.title=`§${id} ${t(book.title)} · ${t(['抽象代数 I','Abstract Algebra I'])}`;
scene.dataset.lessonScene=e.id;const u=new URL(location.href);u.hash=e.id;history.replaceState(null,'',u);
if(e.id==='check')quiz(scene);else{
scene.innerHTML=`<div class="notebook-visual">${e.visual?'<div class="group-demo"></div>':`<div class="group-focus">${formula(e.tex)}<p>${t(e.title)}</p></div>`}</div><section class="notebook-exposition">${e.proof?'<div class="group-proof"></div>':''}${e.example?`<article class="group-example"><h3>${t(['例子与应用','Example and application'])}</h3><p>${html(e.example)}</p></article>`:''}${e.extraProof?`<details class="group-detail"><summary>${t(['补充论证','Supporting argument'])}</summary>${e.extraProof.map(s=>`<p>${html(s)}</p>`).join('')}</details>`:''}${e.warning?`<aside class="group-warning"><h3>${t(['注意条件','Check the hypotheses'])}</h3><p>${html(e.warning)}</p></aside>`:''}<p class="group-recap">${t(['课堂任务：用自己的话解释左侧结论；指出一个关键条件，并举例说明。','Class task: explain the statement in your own words, identify a key hypothesis, and give an example.'])}</p></section>`;
if(e.visual)window.GroupVisuals.render(scene.querySelector('.group-demo'),e.visual);
if(e.proof)proofPanel(scene.querySelector('.group-proof'),e.proof);
}
window.dispatchEvent(new Event('lesson-rendered'));
}
window.LessonBook={id,title:book.title[0],titleEn:book.title[1],navigate(topic){const i=entries.findIndex(e=>e.id===topic);if(i>=0)show(i);}};
window.addEventListener('hashchange',()=>{const i=entries.findIndex(e=>e.id===location.hash.slice(1));if(i>=0&&i!==current)show(i);});
window.addEventListener('course-language',()=>show(current));
document.addEventListener('keydown',event=>{if(event.altKey||event.ctrlKey||event.metaKey||event.shiftKey||event.target.closest('input,textarea,select,button,summary,[contenteditable]'))return;if(event.key==='ArrowRight'||event.key==='ArrowLeft'){event.preventDefault();window.LessonScreen?.step(event.key==='ArrowRight'?1:-1);}});
$('previous').onclick=()=>show(current-1);$('next').onclick=()=>show(current+1);
$('reference-reading').textContent=`《近世代数》第三版 §${id}。${book.optional?'拓展阅读。':''}`;
const initial=entries.findIndex(e=>e.id===location.hash.slice(1));show(initial<0?0:initial);
})();
