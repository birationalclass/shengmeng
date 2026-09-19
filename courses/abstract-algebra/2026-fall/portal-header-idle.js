/* Stable toolbar hit targets, restrained feedback, and bilingual explanations. */
(()=>{
  'use strict';
  const header=document.querySelector('.portal-header');if(!header)return;
  const finePointer=matchMedia('(hover:hover) and (pointer:fine)');
  const phone=matchMedia('(max-width:767px), (pointer:coarse) and (max-width:1024px)');
  const tip=document.createElement('div');tip.id='portal-control-tip';tip.className='portal-control-tip';tip.setAttribute('role','tooltip');tip.hidden=true;document.body.append(tip);
  let timer=0,tipTimer=0,current=null;
  function hideTip(){clearTimeout(tipTimer);current?.removeAttribute('aria-describedby');current=null;tip.hidden=true;}
  function description(button){
    const en=window.CourseLanguage?.language==='en',t=(zh,english)=>en?english:zh;
    switch(button.id){
      case 'portal-course-open':return [t('课程安排','Course schedule'),t('返回本学期课表与课程介绍','Return to the semester schedule and overview')];
      case 'portal-directory-open':return [t('教材目录','Textbook contents'),t('按章节选择课件与知识点','Choose a section or topic')];
      case 'portal-language':return [en?'切换为中文':'Switch to English',t('切换课程页面与当前课件的语言','Change the course and current lesson language')];
      case 'portal-fullscreen':return [document.fullscreenElement?t('退出全屏','Exit fullscreen'):t('全屏显示','Enter fullscreen'),document.fullscreenElement?t('点击按钮或按 Esc 返回窗口','Click or press Esc to return to the window'):t('扩大阅读区域，保留顶部导航','Expand the reading area and keep navigation available')];
      case 'portal-settings':return [t('页面设置','Page settings'),t('调整配色与沙粒动态效果','Adjust the appearance and sand animation')];
      case 'portal-prev':return [t('上一小节','Previous section'),button.textContent.replace(/^←\s*/, '')];
      case 'portal-next':return [t('下一小节','Next section'),button.textContent.replace(/\s*→$/, '')];
      default:return [button.getAttribute('aria-label')||button.textContent,''];
    }
  }
  function showTip(button,immediate=false){
    hideTip();if(button.hidden||button.disabled)return;
    current=button;
    tipTimer=setTimeout(()=>{
      if(current!==button||document.querySelector('dialog[open]'))return;
      const [title,detail]=description(button),heading=document.createElement('strong'),text=document.createElement('span');heading.textContent=title;text.textContent=detail;
      tip.replaceChildren(heading,text);tip.hidden=false;button.setAttribute('aria-describedby',tip.id);
      const rect=button.getBoundingClientRect(),box=tip.getBoundingClientRect();
      tip.style.left=Math.max(8,Math.min(innerWidth-box.width-8,rect.left+rect.width/2-box.width/2))+'px';
      tip.style.top=Math.min(innerHeight-box.height-8,rect.bottom+10)+'px';
    },immediate?0:220);
  }
  function wake(){
    clearTimeout(timer);header.classList.remove('is-idle');
    if(!finePointer.matches||phone.matches||document.hidden)return;
    timer=setTimeout(()=>{
      if(!document.querySelector('dialog[open]')&&!header.matches(':hover')&&!header.querySelector(':focus-visible'))header.classList.add('is-idle');
    },2400);
  }
  function listen(target){
    if(!target)return;
    for(const type of ['pointermove','pointerdown','keydown','focusin','focusout'])target.addEventListener(type,wake,{passive:true});
  }
  listen(document);
  // Frames are created and destroyed on navigation; never retain their windows.
  const observed=new WeakSet();
  function observeFrame(){
    const frame=document.getElementById('lecture-frame');if(!frame||observed.has(frame))return;
    observed.add(frame);frame.addEventListener('load',()=>{listen(frame.contentDocument);wake();});
    listen(frame.contentDocument);
  }
  new MutationObserver(observeFrame).observe(document.getElementById('portal-content'),{childList:true});observeFrame();
  header.querySelectorAll('button').forEach(button=>{
    // Custom tooltips replace slow native titles and do not intercept pointer hits.
    button.removeAttribute('title');
    button.addEventListener('pointerenter',event=>{wake();if(event.pointerType!=='touch')showTip(button);});
    button.addEventListener('pointerleave',hideTip);
    button.addEventListener('focus',()=>{wake();if(button.matches(':focus-visible'))showTip(button,true);});
    button.addEventListener('blur',hideTip);
    button.addEventListener('pointerdown',hideTip);
    button.addEventListener('click',()=>{hideTip();wake();});
  });
  header.addEventListener('pointerleave',wake);
  document.addEventListener('keydown',event=>{if(event.key==='Escape')hideTip();});
  const reset=()=>{hideTip();wake();header.querySelectorAll('[title]').forEach(button=>button.removeAttribute('title'));};
  document.addEventListener('close',reset,true);document.addEventListener('visibilitychange',reset);
  document.addEventListener('fullscreenchange',reset);
  window.addEventListener('course-language',reset);window.addEventListener('resize',reset);
  window.addEventListener('focus',wake);window.addEventListener('blur',hideTip);
  finePointer.addEventListener('change',reset);phone.addEventListener('change',reset);
  new MutationObserver(reset).observe(document.body,{attributes:true,attributeFilter:['class']});
  wake();
})();
