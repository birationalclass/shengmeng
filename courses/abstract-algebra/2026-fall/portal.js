/* A stable course URL hosts the schedule and the interactive textbook lesson. */
(()=>{
  'use strict';
  const $=id=>document.getElementById(id),body=document.body;
  const chapters=[{id:'1.1',title:['等价关系与集合的分类','Equivalence relations and partitions'],topics:[['relation','等价关系','Equivalence relations'],['quotient','等价类','Equivalence classes'],['partition','集合的分类','Partitions'],['check','教材习题','Textbook exercises']]},{id:'1.2',title:['群的概念','The concept of a group'],topics:[['operation','代数运算','Binary operations'],['axioms','群的公理','Group axioms'],['symmetry','对称与群','Symmetries'],['properties','基本性质','Basic properties'],['powers','方幂与指数','Integer powers'],['criteria','群的判别','Recognizing groups'],['check','教材习题','Textbook exercises']]}];
  const sections=window.CourseSections;
  sections.forEach(section=>section.topics=chapters.find(c=>c.id===section.id)?.topics||[['blank','空白测试页','Blank test page']]);
  window.CourseLanguage.add(Object.fromEntries(sections.map(s=>s.title)));
  const chapterNames=[['群','Groups'],['群的进一步讨论','Further group theory'],['环','Rings'],['环的进一步讨论','Further ring theory']];
  const scheduleTranslations={};document.querySelectorAll('#schedule tbody tr').forEach((row,i)=>{const pair=window.CourseScheduleEnglish[i];if(!pair)return;const title=row.querySelector('h3'),focus=row.querySelector('.focus');if(title)scheduleTranslations[title.textContent.trim()]=pair[0]+(title.querySelector('a')?' ↗':'');scheduleTranslations[focus.textContent.trim()]=pair[1];});window.CourseLanguage.add(scheduleTranslations);
  const en=()=>window.CourseLanguage?.language==='en',t=(zh,english)=>en()?english:zh;
  body.classList.add('course-portal');
  const header=document.createElement('header');header.className='portal-header';
  header.innerHTML='<button id="portal-course-open" class="portal-icon" type="button"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m3 10 9-7 9 7v10a1 1 0 0 1-1 1h-5v-7H9v7H4a1 1 0 0 1-1-1Z"/></svg></button><a class="portal-brand" href="?view=course">代数学 Ⅰ</a><button id="portal-directory-open" type="button"></button><nav class="portal-section-nav" aria-label="教材小节导航"><button id="portal-prev" type="button"></button><button id="portal-next" type="button"></button></nav><button id="portal-language" type="button"></button><button id="portal-fullscreen" type="button"></button><button id="portal-settings" class="portal-icon" type="button" aria-haspopup="dialog" aria-controls="pageStyleSettings"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m9.5 3-.7 2.7-2 .9-2.5-.7-2 3.4 1.8 2v2.4l-1.8 2 2 3.4 2.5-.7 2 .9.7 2.7h5l.7-2.7 2-.9 2.5.7 2-3.4-1.8-2v-2.4l1.8-2-2-3.4-2.5.7-2-.9-.7-2.7Z"/><circle cx="12" cy="12" r="3"/></svg></button>';
  $('main').before(header);
  const content=document.createElement('div');content.id='portal-content';content.innerHTML='<section id="lecture-placeholder" hidden><div><p class="placeholder-number"></p><h1></h1><p class="placeholder-state"></p></div></section><iframe id="lecture-frame" title="抽象代数交互课件" allow="fullscreen" hidden></iframe>';body.append(content);
  const directory=document.createElement('dialog');directory.className='portal-directory';directory.setAttribute('aria-labelledby','portal-directory-title');directory.innerHTML='<div class="portal-directory-header"><h2 id="portal-directory-title"></h2><button class="portal-close" type="button" aria-label="关闭目录">×</button></div><label class="portal-directory-select"><select id="portal-directory-chapter" aria-label="选择教材章节"></select></label><div class="portal-directory-grid"></div><div class="portal-directory-pages"><button type="button" id="directory-prev">←</button><span id="directory-count"></span><button type="button" id="directory-next">→</button></div>';body.append(directory);
  let view='course',section='1.1',anchor='relation',loadedSection='',courseScroll=0,directoryChapter=1,directoryPage=0;
  const phone=matchMedia('(max-width:767px), (pointer:coarse) and (max-width:1024px)');
  const frame=$('lecture-frame');
  const link=(book,topic)=>`?view=lesson&section=${book}#${topic}`;
  function labels(){
    document.title=t('代数学 Ⅰ · 2026 秋季 · 孟晟','Algebra Ⅰ · Autumn 2026 · Sheng Meng');
    $('portal-directory-open').textContent=t('目录','Contents');const current=sections.findIndex(s=>s.id===section),previous=view==='lesson'?sections[current-1]:null,next=sections[view==='lesson'?current+1:0];$('portal-prev').hidden=!previous;$('portal-next').hidden=!next;const name=s=>`§${s.id} ${s.title[en()?1:0]}`;$('portal-prev').textContent=previous?'← '+name(previous):'';$('portal-next').textContent=next?name(next)+' →':'';const brand=header.querySelector('.portal-brand');brand.textContent=view==='lesson'?name(sections[current]):t('代数学 Ⅰ','Algebra Ⅰ');brand.title=brand.textContent;brand.setAttribute('href',view==='lesson'?link(section,anchor):'?view=course');$('portal-course-open').setAttribute('aria-label',t('课程安排','Course'));$('portal-course-open').title=t('课程安排','Course');$('portal-language').textContent=en()?'中文':'EN';$('portal-language').setAttribute('aria-label',t('切换到英文','Switch to Chinese'));$('portal-settings').setAttribute('aria-label',t('设置','Settings'));$('portal-settings').title=t('设置','Settings');$('portal-directory-title').textContent=t('教材目录','Textbook contents');
    directory.querySelector('.portal-close').setAttribute('aria-label',t('关闭目录','Close contents'));
    $('portal-directory-chapter').innerHTML=chapterNames.map((names,i)=>`<option value="${i+1}">${t('第 '+(i+1)+' 章','Chapter '+(i+1))} · ${names[en()?1:0]}</option>`).join('');$('portal-directory-chapter').value=directoryChapter;directoryItems();
    $('portal-fullscreen').hidden=phone.matches;$('portal-fullscreen').textContent=document.fullscreenElement?t('退出全屏','Exit fullscreen'):t('全屏','Fullscreen');
    frame.title=t('抽象代数交互课件','Interactive abstract algebra lesson');
    if(view==='lesson'&&!sections.find(s=>s.id===section).ready)placeholder();
  }
  function directoryItems(){
    const entries=sections.filter(s=>s.id.startsWith(directoryChapter+'.')),total=Math.ceil(entries.length/4);directoryPage=Math.min(directoryPage,total-1);
    directory.querySelector('.portal-directory-grid').innerHTML=entries.slice(directoryPage*4,directoryPage*4+4).map(s=>`<a href="${link(s.id,s.topics[0][0])}" aria-current="${s.id===section?'page':'false'}"><span>§${s.id}</span><span>${s.title[en()?1:0]}</span>${s.ready?'':`<small>${t('空白测试','Blank test')}</small>`}</a>`).join('');
    $('directory-count').textContent=`${directoryPage+1} / ${total}`;$('directory-prev').disabled=directoryPage===0;$('directory-next').disabled=directoryPage===total-1;
  }
  function placeholder(){const entry=sections.find(s=>s.id===section),panel=$('lecture-placeholder');panel.querySelector('.placeholder-number').textContent=`§${entry.id}`;panel.querySelector('h1').textContent=entry.title[en()?1:0];panel.querySelector('.placeholder-state').textContent=t('空白测试页','Blank test page');}
  function navigate(next,replace=false){
    if(view==='course')courseScroll=window.scrollY;
    view=next.view==='lesson'?'lesson':'course';section=sections.some(c=>c.id===next.section)?next.section:'1.1';const chapter=sections.find(c=>c.id===section);anchor=chapter.topics.some(topic=>topic[0]===next.anchor)?next.anchor:chapter.topics[0][0];
    const url=new URL(location.href);url.searchParams.delete('v');url.searchParams.set('view',view);view==='lesson'?url.searchParams.set('section',section):url.searchParams.delete('section');url.hash=view==='lesson'?anchor:(next.courseHash||'');
    history[replace?'replaceState':'pushState'](null,'',url);
    frame.hidden=view!=='lesson'||!chapter.ready;$('lecture-placeholder').hidden=view!=='lesson'||chapter.ready;content.hidden=view!=='lesson';body.classList.toggle('portal-lesson',view==='lesson');
    if(view==='lesson'){
      window.CourseOpeningExit?.();window.CourseOpeningBoot?.dismiss();
      if(!chapter.ready){placeholder();}
      else if(loadedSection!==section){loadedSection=section;frame.src=`lesson-1/?embedded=1&section=${section}&lang=${en()?'en':'zh'}#${anchor}`;}
      else frame.contentWindow?.postMessage({type:'course-navigate',section,anchor},location.origin);
    }else requestAnimationFrame(()=>{if(next.courseHash)document.getElementById(next.courseHash)?.scrollIntoView();else window.scrollTo(0,courseScroll);});labels();
  }
  function fromURL(){const url=new URL(location.href);navigate({view:url.searchParams.get('view'),section:url.searchParams.get('section'),anchor:url.hash==='#order'?'powers':url.hash.slice(1),courseHash:url.searchParams.get('view')==='lesson'?'':url.hash.slice(1)},true);}
  $('portal-directory-open').onclick=()=>{directoryChapter=Number(section.split('.')[0]);directoryPage=Math.floor((Number(section.split('.')[1])-1)/4);labels();directory.showModal();};$('portal-directory-chapter').onchange=e=>{directoryChapter=+e.target.value;directoryPage=0;directoryItems();};$('directory-prev').onclick=()=>{directoryPage--;directoryItems();};$('directory-next').onclick=()=>{directoryPage++;directoryItems();};directory.querySelector('.portal-close').onclick=()=>directory.close();
  document.addEventListener('click',event=>{const a=event.target.closest('a');if(!a)return;const url=new URL(a.href,location.href);if(url.origin!==location.origin)return;if(url.searchParams.get('view')==='lesson'||url.pathname.endsWith('/lesson-1/')){event.preventDefault();directory.close();navigate({view:'lesson',section:url.searchParams.get('section'),anchor:url.hash.slice(1)});}});
  function adjacent(delta){const index=view==='course'?-1:sections.findIndex(s=>s.id===section),target=sections[index+delta];if(target)navigate({view:'lesson',section:target.id,anchor:target.topics[0][0]});}$('portal-prev').onclick=()=>adjacent(-1);$('portal-next').onclick=()=>adjacent(1);$('portal-course-open').onclick=()=>navigate({view:'course'});header.querySelector('.portal-brand').onclick=event=>{event.preventDefault();navigate({view:'course'});};
  $('portal-settings').onclick=()=>document.querySelector('[data-page-style-open]').click();$('portal-language').onclick=()=>window.CourseLanguage?.set(en()?'zh':'en');
  $('portal-fullscreen').onclick=async()=>{if(phone.matches)return;try{if(document.fullscreenElement)await document.exitFullscreen();else await document.documentElement.requestFullscreen?.();}catch{}labels();};
  document.addEventListener('fullscreenchange',labels);phone.addEventListener('change',()=>{if(phone.matches&&document.fullscreenElement)document.exitFullscreen().catch(()=>{});labels();});
  window.addEventListener('popstate',fromURL);
  window.addEventListener('message',event=>{if(event.origin!==location.origin||event.source!==frame.contentWindow)return;const data=event.data;if(data?.type==='lesson-location'&&data.section===section){anchor=data.anchor;const url=new URL(location.href);url.hash=anchor;history.replaceState(null,'',url);}if(data?.type==='course-route')navigate({view:data.view,section:data.section,anchor:data.anchor});});
  window.addEventListener('course-language',()=>{labels();frame.contentWindow?.postMessage({type:'course-language',language:en()?'en':'zh'},location.origin);});
  function upcomingLabel(){
    document.querySelectorAll('#schedule tr.upcoming .focus').forEach(cell=>{
      if(cell.querySelector('.upcoming-watermark'))return;
      const label=document.createElement('span');label.className='upcoming-watermark';label.textContent='即将到来';cell.append(label);
    });
  }
  if(document.readyState==='complete')upcomingLabel();else document.addEventListener('DOMContentLoaded',upcomingLabel,{once:true});
  labels();fromURL();
})();
