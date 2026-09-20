/* A stable course URL hosts the schedule and the interactive textbook lesson. */
(()=>{
  'use strict';
  const $=id=>document.getElementById(id),body=document.body;
  const chapters=[{id:'1.1',title:['等价关系与集合的分类','Equivalence relations and partitions'],topics:[['relation','等价关系','Equivalence relations'],['quotient','等价类','Equivalence classes'],['partition','集合的分类','Partitions'],['check','自测','Self-check']]},{id:'1.2',title:['群的概念','The concept of a group'],topics:[['operation','代数运算','Binary operations'],['axioms','群的公理','Group axioms'],['one-sided','单侧公理','One-sided axioms'],['symmetry','对称与群','Symmetries'],['properties','基本性质','Basic properties'],['powers','方幂与指数','Integer powers'],['criteria','群的判别','Recognizing groups'],['check','自测','Self-check']]}];
  const sections=window.CourseSections;
  sections.forEach(section=>{section.topics=chapters.find(c=>c.id===section.id)?.topics||window.GroupSections?.[section.id]?.topics||[['blank','空白测试页','Blank test page']];section.optional=!!window.GroupSections?.[section.id]?.optional;});
  window.CourseLanguage.add(Object.fromEntries(sections.map(s=>s.title)));
  const chapterNames=[['群','Groups'],['群的进一步讨论','Further group theory'],['环','Rings'],['环的进一步讨论','Further ring theory']];
  const scheduleTranslations={};document.querySelectorAll('#schedule tbody tr').forEach((row,i)=>{const pair=window.CourseScheduleEnglish[i];if(!pair)return;const title=row.querySelector('h3'),focus=row.querySelector('.focus');if(title)scheduleTranslations[title.textContent.trim()]=pair[0]+(title.querySelector('a')?' ↗':'');scheduleTranslations[focus.textContent.trim()]=pair[1];});window.CourseLanguage.add(scheduleTranslations);
  const en=()=>window.CourseLanguage?.language==='en',t=(zh,english)=>en()?english:zh;
  body.classList.add('course-portal');
  const header=document.createElement('header');header.className='portal-header';header.setAttribute('aria-label','课程导航');
  header.innerHTML='<button id="portal-course-open" class="portal-icon" type="button"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m3 10 9-7 9 7v10a1 1 0 0 1-1 1h-5v-7H9v7H4a1 1 0 0 1-1-1Z"/></svg></button><span class="portal-brand">代数学 Ⅰ</span><button id="portal-directory-open" type="button"></button><nav class="portal-section-nav" aria-label="教材小节导航"><button id="portal-prev" type="button"></button><button id="portal-next" type="button"></button></nav><button id="portal-language" type="button"></button><button id="portal-fullscreen" class="portal-icon" type="button"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" aria-hidden="true"><rect class="portal-fullscreen-expand" x="4" y="4" width="16" height="16" rx="1"/><rect class="portal-fullscreen-restore" x="8" y="8" width="8" height="8" rx=".5" fill="currentColor"/></svg></button><button id="portal-settings" class="portal-icon" type="button" aria-haspopup="dialog" aria-controls="pageStyleSettings"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="m9.5 3-.7 2.7-2 .9-2.5-.7-2 3.4 1.8 2v2.4l-1.8 2 2 3.4 2.5-.7 2 .9.7 2.7h5l.7-2.7 2-.9 2.5.7 2-3.4-1.8-2v-2.4l1.8-2-2-3.4-2.5.7-2-.9-.7-2.7Z"/><circle cx="12" cy="12" r="3"/></svg></button>';
  $('main').before(header);
  const content=document.createElement('div');content.id='portal-content';content.innerHTML='<section id="lecture-placeholder" hidden><div><p class="placeholder-number"></p><h1></h1><p class="placeholder-state"></p></div></section>';body.append(content);
  const directory=document.createElement('dialog');directory.className='portal-directory';directory.setAttribute('aria-labelledby','portal-directory-title');directory.innerHTML='<div class="portal-directory-header"><h2 id="portal-directory-title"></h2><button class="portal-close" type="button" aria-label="关闭目录">×</button></div><div class="portal-directory-layout"><section class="directory-map-section"><label class="portal-directory-select"><select id="portal-directory-chapter" aria-label="选择教材章节"></select></label><div class="directory-map" role="group"><svg class="directory-routes directory-routes-wide" viewBox="0 0 1000 520" preserveAspectRatio="none" aria-hidden="true"></svg><svg class="directory-routes directory-routes-narrow" preserveAspectRatio="none" aria-hidden="true"></svg><div class="directory-nodes"></div></div><p class="directory-map-caption"></p></section><aside class="directory-detail" aria-live="polite"></aside></div>';body.append(directory);
  let view='course',section='1.1',anchor='relation',loadedSection='',courseScroll=0,directoryChapter=1,directorySelected='1.1';
  const phone=matchMedia('(max-width:767px), (pointer:coarse) and (max-width:1024px)');
  let frame=null;
  const courseScroller=$('course-scroll-region');
  function releaseLesson(){
    // Removing the browsing context cancels its requests and disposes timers,
    // event listeners, canvas contexts and section data. Do not cache windows.
    if(frame){frame.remove();frame=null;}
    loadedSection='';
  }
  document.querySelector('.course-title-panel').addEventListener('wheel',event=>{if(view!=='course'||event.ctrlKey||document.querySelector('dialog[open]'))return;const unit=event.deltaMode===1?20:event.deltaMode===2?courseScroller.clientHeight:1;courseScroller.scrollBy({top:event.deltaY*unit,behavior:'instant'});event.preventDefault();},{passive:false});
  function scrollCourse(hash,behavior='smooth'){const target=document.getElementById(hash);if(!target)return;const top=courseScroller.contains(target)?courseScroller.scrollTop+target.getBoundingClientRect().top-courseScroller.getBoundingClientRect().top-20:0;courseScroller.scrollTo({top,behavior});window.scrollTo(0,0);}
  const link=(book,topic)=>`?view=lesson&section=${book}#${topic}`;
  function labels(){
    header.setAttribute('aria-label',t('课程导航','Course navigation'));
    courseScroller.setAttribute('aria-label',t('课程介绍与安排','Course introduction and schedule'));
    document.title=t('代数学 Ⅰ · 2026 秋季 · 孟晟','Algebra Ⅰ · Autumn 2026 · Sheng Meng');
    $('portal-directory-open').textContent=t('目录','Contents');const current=sections.findIndex(s=>s.id===section),previous=view==='lesson'?sections[current-1]:null,next=sections[view==='lesson'?current+1:0];$('portal-prev').hidden=!previous;$('portal-next').hidden=!next;const name=s=>`§${s.id} ${s.title[en()?1:0]}`;$('portal-prev').textContent=previous?'← '+name(previous):'';$('portal-next').textContent=next?name(next)+' →':'';const brand=header.querySelector('.portal-brand');brand.textContent=view==='lesson'?name(sections[current]):t('代数学 Ⅰ','Algebra Ⅰ');brand.title=brand.textContent;$('portal-course-open').setAttribute('aria-label',t('课程安排','Course'));$('portal-course-open').title=t('课程安排','Course');$('portal-language').textContent=en()?'中文':'EN';$('portal-language').setAttribute('aria-label',t('切换到英文','Switch to Chinese'));$('portal-settings').setAttribute('aria-label',t('设置','Settings'));$('portal-settings').title=t('设置','Settings');$('portal-directory-title').textContent=t('教材目录','Textbook contents');
    directory.querySelector('.portal-close').setAttribute('aria-label',t('关闭目录','Close contents'));
    $('portal-directory-chapter').setAttribute('aria-label',t('选择教材章节','Choose a textbook chapter'));$('portal-directory-chapter').innerHTML=chapterNames.map((names,i)=>`<option value="${i+1}">${t('第 '+(i+1)+' 章','Chapter '+(i+1))} · ${names[en()?1:0]}</option>`).join('');$('portal-directory-chapter').value=directoryChapter;directoryItems();
    const fullscreenButton=$('portal-fullscreen'),fullscreenActive=!!document.fullscreenElement,fullscreenLabel=fullscreenActive?t('退出全屏','Exit fullscreen'):t('全屏','Fullscreen');fullscreenButton.hidden=phone.matches;fullscreenButton.setAttribute('aria-label',fullscreenLabel);fullscreenButton.title=fullscreenLabel;fullscreenButton.setAttribute('aria-pressed',String(fullscreenActive));
    if(frame)frame.title=t('抽象代数交互课件','Interactive abstract algebra lesson');
    if(view==='lesson'&&!sections.find(s=>s.id===section).ready)placeholder();
  }
  function directoryDetail(){
    const entry=sections.find(s=>s.id===directorySelected),name=entry.title[en()?1:0];
    directory.querySelector('.directory-detail').innerHTML=`<span class="directory-detail-number">§${entry.id}</span><h3>${name}</h3><p class="directory-availability">${entry.id===section?t('正在阅读','Currently reading'):entry.ready?(entry.optional?t('课件已开放 · 拓展阅读','Lesson available · Optional'):t('课件已开放','Lesson available')):t('待更新','Coming soon')}</p><div class="directory-topic-list">${entry.ready?entry.topics.map(topic=>`<a href="${link(entry.id,topic[0])}">${topic[0]==='check'?'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" aria-hidden="true"><rect x="5" y="4" width="14" height="17" rx="2"/><path d="M9 4V2h6v2M8 11l2 2 5-5M8 17h8"/></svg>':'<span class="directory-topic-dot" aria-hidden="true"></span>'}<span>${topic[en()?2:1]}</span><span aria-hidden="true">↗</span></a>`).join(''):t('本节课件正在准备中。','Materials for this section are being prepared.')}</div>${entry.ready?`<a class="directory-enter" href="${link(entry.id,entry.topics[0][0])}">${t('进入课件','Open lesson')}<span aria-hidden="true">→</span></a>`:`<span class="directory-enter is-unavailable">${t('尚未开放','Not yet available')}</span>`}`;
    directory.querySelectorAll('[data-directory-section]').forEach(node=>{const active=node.dataset.directorySection===entry.id;node.classList.toggle('is-selected',active);node.setAttribute('aria-pressed',String(active));});
  }
  function directoryItems(){
    const entries=sections.filter(s=>s.id.startsWith(directoryChapter+'.'));
    if(!entries.some(s=>s.id===directorySelected))directorySelected=entries[0].id;
    const ys=[365,220,360,145,305,150,275],coords=entries.map((s,i)=>[85+i*830/(entries.length-1),ys[i]]);
    const narrow=entries.map((s,i)=>[i%2?68:30,55+i*124]);
    const paths=(points,vertical=false)=>points.slice(0,-1).map((p,i)=>{const q=points[i+1],m=vertical?(p[1]+q[1])/2:(p[0]+q[0])/2;return `<path d="M${p[0]} ${p[1]} C${vertical?p[0]:m} ${vertical?m:p[1]},${vertical?q[0]:m} ${vertical?m:q[1]},${q[0]} ${q[1]}"/>`;}).join('');
    directory.querySelector('.directory-routes-wide').innerHTML=paths(coords);
    const svg=directory.querySelector('.directory-routes-narrow');svg.setAttribute('viewBox',`0 0 100 ${entries.length*124}`);svg.innerHTML=paths(narrow,true);
    const map=directory.querySelector('.directory-map');map.style.setProperty('--route-height',`${entries.length*124}px`);map.setAttribute('aria-label',t('教材章节路径','Textbook section path'));
    directory.querySelector('.directory-nodes').innerHTML=entries.map((entry,i)=>`<button type="button" class="directory-node ${entry.ready?'is-ready':''}" data-directory-section="${entry.id}" style="--node-x:${coords[i][0]/10}%;--node-y:${coords[i][1]/5.2}%;--node-mobile-x:${narrow[i][0]}%;--node-mobile-y:${narrow[i][1]}px" aria-label="§${entry.id} ${entry.title[en()?1:0]}" ${entry.id===section?'aria-current="page"':''}><span class="directory-node-orb">${entry.id}</span><span class="directory-node-label">${entry.title[en()?1:0]}</span></button>`).join('');
    directory.querySelector('.directory-map-caption').textContent=t('按教材顺序 · 点选小节查看内容','Textbook order · Select a section to explore');
    directoryDetail();
  }
  function placeholder(){const entry=sections.find(s=>s.id===section),panel=$('lecture-placeholder');panel.querySelector('.placeholder-number').textContent=`§${entry.id}`;panel.querySelector('h1').textContent=entry.title[en()?1:0];panel.querySelector('.placeholder-state').textContent=t('空白测试页','Blank test page');}
  function navigate(next,replace=false){
    if(view==='course')courseScroll=courseScroller.scrollTop;
    view=next.view==='lesson'?'lesson':'course';section=sections.some(c=>c.id===next.section)?next.section:'1.1';const chapter=sections.find(c=>c.id===section);anchor=chapter.topics.some(topic=>topic[0]===next.anchor)?next.anchor:chapter.topics[0][0];
    const url=new URL(location.href);url.searchParams.delete('v');url.searchParams.set('view',view);view==='lesson'?url.searchParams.set('section',section):url.searchParams.delete('section');url.hash=view==='lesson'?anchor:(next.courseHash||'');
    history[replace?'replaceState':'pushState'](null,'',url);
    if(view!=='lesson'||!chapter.ready||loadedSection!==section)releaseLesson();$('lecture-placeholder').hidden=view!=='lesson'||chapter.ready;content.hidden=view!=='lesson';body.classList.toggle('portal-lesson',view==='lesson');
    if(view==='lesson'){
      window.CourseOpeningExit?.();window.CourseOpeningBoot?.dismiss();
      if(!chapter.ready){placeholder();}
      else if(!frame){loadedSection=section;frame=document.createElement('iframe');frame.id='lecture-frame';frame.allow='fullscreen';frame.src=`${window.GroupSections?.[section]?'lesson-groups':'lesson-1'}/?v=20260920-unit-tables-v2&embedded=1&section=${section}&lang=${en()?'en':'zh'}#${anchor}`;content.append(frame);}
      else frame?.contentWindow?.postMessage({type:'course-navigate',section,anchor},location.origin);
    }else requestAnimationFrame(()=>{if(next.courseHash)scrollCourse(next.courseHash,'instant');else courseScroller.scrollTo({top:courseScroll,behavior:'instant'});});labels();
  }
  function fromURL(){const url=new URL(location.href);navigate({view:url.searchParams.get('view'),section:url.searchParams.get('section'),anchor:url.hash==='#order'?'powers':url.hash.slice(1),courseHash:url.searchParams.get('view')==='lesson'?'':url.hash.slice(1)},true);}
  $('portal-directory-open').onclick=()=>{directoryChapter=Number(section.split('.')[0]);directorySelected=section;labels();directory.showModal();};
  $('portal-directory-chapter').onchange=e=>{directoryChapter=+e.target.value;directoryItems();};
  directory.querySelector('.directory-nodes').onclick=e=>{const node=e.target.closest('[data-directory-section]');if(node){directorySelected=node.dataset.directorySection;directoryDetail();}};
  directory.querySelector('.portal-close').onclick=()=>directory.close();
  document.addEventListener('click',event=>{const a=event.target.closest('a');if(!a)return;const url=new URL(a.href,location.href);if(url.origin!==location.origin)return;if(view==='course'&&url.pathname===location.pathname&&url.hash&&url.searchParams.get('view')!=='lesson'){const target=document.getElementById(url.hash.slice(1));if(target&&(target.id==='main'||courseScroller.contains(target))){event.preventDefault();history.pushState(null,'',url);scrollCourse(target.id);return;}}if(url.searchParams.get('view')==='lesson'||(url.pathname.endsWith('/lesson-1/')||url.pathname.endsWith('/lesson-groups/'))){event.preventDefault();directory.close();navigate({view:'lesson',section:url.searchParams.get('section'),anchor:url.hash.slice(1)});}});
  function adjacent(delta){const index=view==='course'?-1:sections.findIndex(s=>s.id===section),target=sections[index+delta];if(target)navigate({view:'lesson',section:target.id,anchor:target.topics[0][0]});}$('portal-prev').onclick=()=>adjacent(-1);$('portal-next').onclick=()=>adjacent(1);$('portal-course-open').onclick=()=>navigate({view:'course'});
  $('portal-settings').onclick=()=>document.querySelector('[data-page-style-open]').click();$('portal-language').onclick=()=>window.CourseLanguage?.set(en()?'zh':'en');
  $('portal-fullscreen').onclick=async()=>{if(phone.matches)return;try{if(document.fullscreenElement)await document.exitFullscreen();else await document.documentElement.requestFullscreen?.();}catch{}labels();};
  document.addEventListener('fullscreenchange',labels);phone.addEventListener('change',()=>{if(phone.matches&&document.fullscreenElement)document.exitFullscreen().catch(()=>{});labels();});
  window.addEventListener('popstate',fromURL);
  window.addEventListener('message',event=>{if(event.origin!==location.origin||event.source!==frame?.contentWindow)return;const data=event.data;if(data?.type==='lesson-location'&&data.section===section){anchor=data.anchor;const url=new URL(location.href);url.hash=anchor;history.replaceState(null,'',url);}if(data?.type==='course-route')navigate({view:data.view,section:data.section,anchor:data.anchor});});
  window.addEventListener('course-language',()=>{labels();frame?.contentWindow?.postMessage({type:'course-language',language:en()?'en':'zh'},location.origin);});
  function upcomingLabel(){
    document.querySelectorAll('#schedule tr.upcoming .focus').forEach(cell=>{
      if(cell.querySelector('.upcoming-watermark'))return;
      const label=document.createElement('span');label.className='upcoming-watermark';label.textContent='即将到来';cell.append(label);
    });
  }
  if(document.readyState==='complete')upcomingLabel();else document.addEventListener('DOMContentLoaded',upcomingLabel,{once:true});
  labels();fromURL();
})();
