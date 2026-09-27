(()=>{
 const t=pair=>pair[window.CourseLanguage?.language==='en'?1:0];
 const escape=value=>String(value).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
 function mount(root,extension){
  const blocks=items=>items.map(b=>`<p>${escape(t(b.text))}</p>${b.tex?`<div class="construction-math">${katex.renderToString(b.tex,{displayMode:true,throwOnError:true})}</div>`:''}`).join('');
  root.innerHTML=`<div class="card-magic-notebook"><p class="card-magic-entry"><a href="../../card-magic/?lang=${window.CourseLanguage?.language==='en'?'en':'zh'}" target="_top">${t(['进入纸牌魔术交互实验室 ↗','Open the card-magic laboratory ↗'])}</a></p>${extension.tricks.map((trick,i)=>`<article class="construction-step"><h3>${String(i+1).padStart(2,'0')} · ${escape(t(trick.title))}</h3><p>${escape(t(trick.effect))}</p><p class="construction-overview">${escape(t(trick.connection))}</p><p><a href="../../card-magic/?lang=${window.CourseLanguage?.language==='en'?'en':'zh'}#${trick.id}" target="_top">${t(['亲手演示这个魔术 ↗','Try this trick ↗'])}</a></p>${trick.details.map(d=>`<details class="construction-disclosure"><summary><span class="construction-sign" aria-hidden="true"></span><span>${escape(t(d.title))}</span></summary><div class="construction-disclosure-body">${blocks(d.blocks)}</div></details>`).join('')}<p class="card-magic-source"><a href="${trick.source.url}" target="_blank" rel="noopener">${escape(t(trick.source.label))} ↗</a></p></article>`).join('')}</div>`;
  root.addEventListener('toggle',()=>requestAnimationFrame(()=>window.LessonScreen?.refresh()),true);
 }
 window.CardMagic={mount};
})();
