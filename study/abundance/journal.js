// Render math without changing the original prose.
if(window.katex){
 for(const host of document.querySelectorAll('.math-text p,.sr-only')){
  const text=host.textContent,pattern=/\$([^$]+)\$|\\\[([\s\S]*?)\\\]|\\\(([\s\S]*?)\\\)/g;
  let end=0,match;const frag=document.createDocumentFragment();
  while((match=pattern.exec(text))){frag.append(document.createTextNode(text.slice(end,match.index)));const span=document.createElement('span');katex.render(match[1]??match[2]??match[3],span,{displayMode:match[2]!==undefined,throwOnError:false,macros:{'\\Q':'\\mathbb{Q}'}});frag.append(span);end=pattern.lastIndex;}
  frag.append(document.createTextNode(text.slice(end)));host.replaceChildren(frag);
 }
}

const messages=[...document.querySelectorAll('.chat-message')];
let explicitDateNavigation=false;
const dateNav=document.querySelector('.date-navigation'),dateToggle=document.querySelector('.date-toggle');
function closeDateNav(){dateNav.dataset.open='false';dateToggle.setAttribute('aria-expanded','false');}
dateToggle.addEventListener('click',()=>{const open=dateToggle.getAttribute('aria-expanded')!=='true';dateNav.dataset.open=String(open);dateToggle.setAttribute('aria-expanded',String(open));if(open)dateNav.querySelector('a')?.focus();});
document.addEventListener('keydown',event=>{if(event.key==='Escape'&&dateNav.dataset.open==='true'){closeDateNav();dateToggle.focus();}});
dateNav.querySelectorAll('a').forEach(link=>link.addEventListener('click',event=>{event.preventDefault();explicitDateNavigation=true;const target=document.getElementById('day-'+link.dataset.date);if(!target)return;dateNav.querySelectorAll('a').forEach(a=>a.removeAttribute('aria-current'));link.setAttribute('aria-current','date');history.replaceState(null,'','#'+target.id);reserveScrollRoom(target,76);target.scrollIntoView({block:'start',behavior:'instant'});closeDateNav();if(matchMedia('(max-width:1279px)').matches)dateToggle.focus({preventScroll:true});}));
function reserveScrollRoom(target,desiredTop){
 const main=document.querySelector('.learning-page');
 main.style.paddingBottom='';
 const base=parseFloat(getComputedStyle(main).paddingBottom)||0;
 const needed=window.scrollY+target.getBoundingClientRect().top-desiredTop+window.innerHeight-document.documentElement.scrollHeight;
 if(needed>0)main.style.paddingBottom=(base+Math.ceil(needed))+'px';
}
function changeLanguage(lang,preserve=true){const anchor=preserve?(messages.find(m=>m.getBoundingClientRect().bottom>20)||messages.at(-1)):null;const top=anchor?.getBoundingClientRect().top;document.querySelectorAll('[data-lang]').forEach(n=>n.hidden=n.dataset.lang!==lang);document.querySelectorAll('[data-language]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.language===lang)));document.documentElement.lang=lang==='zh'?'zh-CN':'en';if(anchor){reserveScrollRoom(anchor,top);window.scrollBy({top:anchor.getBoundingClientRect().top-top,behavior:'instant'});}}
document.querySelectorAll('[data-language]').forEach(b=>b.addEventListener('click',()=>changeLanguage(b.dataset.language)));
async function locateLatest(){await document.fonts.ready;const img=document.querySelector('#sourceTheorem');if(!img.complete)await new Promise(resolve=>{img.addEventListener('load',resolve,{once:true});img.addEventListener('error',resolve,{once:true});});await new Promise(requestAnimationFrame);if(explicitDateNavigation)return;const target=location.hash?document.getElementById(location.hash.slice(1)):messages.at(-1);if(target){reserveScrollRoom(target,24);target.scrollIntoView({block:'start',behavior:'instant'});}}
locateLatest();
