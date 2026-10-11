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
const viewTools=document.querySelector('.chat-view-tools');
const viewButtons=[...viewTools.querySelectorAll('[data-chat-view]')];
const visibleMessages=()=>messages.filter(message=>!message.hidden);
function updateToolLabels(){
 const english=document.documentElement.lang==='en';
 viewTools.setAttribute('aria-label',english?'Chat visibility and reading guide':'聊天显示与阅读指引');
 const guide=viewTools.querySelector('.reading-guide');
 const guideLabel=english?'Reading guide · Jets':'阅读指引 · Jets';
 guide.setAttribute('aria-label',guideLabel);guide.title=guideLabel;
 for(const button of viewButtons){
  const label=button.dataset.chatView==='all'?(english?'All messages':'完整聊天'):(english?'Important messages':'重要聊天');
  button.setAttribute('aria-label',label);button.title=label;
 }
}
function changeChatView(mode){
 const before=visibleMessages();
 const anchor=before.find(message=>message.getBoundingClientRect().bottom>76)||before.at(-1);
 const oldTop=anchor?.getBoundingClientRect().top;
 const oldIndex=messages.indexOf(anchor);
 explicitReadingNavigation=true;
 for(const message of messages)message.hidden=mode==='important'&&!message.matches('.mathematics.highlighted');
 for(const day of document.querySelectorAll('.day-separator')){
  let next=day.nextElementSibling,hasMessages=false;
  while(next&&!next.matches('.day-separator')){if(next.matches('.chat-message')&&!next.hidden)hasMessages=true;next=next.nextElementSibling;}
  day.hidden=!hasMessages;
  const link=dateNav.querySelector('[data-date="'+day.id.slice(4)+'"]');
  if(link){link.hidden=day.hidden;if(day.hidden)link.removeAttribute('aria-current');}
 }
 for(const button of viewButtons)button.setAttribute('aria-pressed',String(button.dataset.chatView===mode));
 document.body.dataset.chatView=mode;
 const after=visibleMessages();
 const target=anchor&&!anchor.hidden?anchor:after.find(message=>messages.indexOf(message)>=oldIndex)||after.at(-1);
 if(target){const top=target===anchor?oldTop:76;reserveScrollRoom(target,top);window.scrollBy({top:target.getBoundingClientRect().top-top,behavior:'instant'});}
}
viewButtons.forEach(button=>button.addEventListener('click',()=>changeChatView(button.dataset.chatView)));
updateToolLabels();
let explicitReadingNavigation=false;
const dateNav=document.querySelector('.date-navigation'),dateToggle=document.querySelector('.date-toggle');
function closeDateNav(){dateNav.dataset.open='false';dateToggle.setAttribute('aria-expanded','false');}
dateToggle.addEventListener('click',()=>{const open=dateToggle.getAttribute('aria-expanded')!=='true';dateNav.dataset.open=String(open);dateToggle.setAttribute('aria-expanded',String(open));if(open)dateNav.querySelector('a')?.focus();});
document.addEventListener('keydown',event=>{if(event.key==='Escape'&&dateNav.dataset.open==='true'){closeDateNav();dateToggle.focus();}});
dateNav.querySelectorAll('a').forEach(link=>link.addEventListener('click',event=>{event.preventDefault();explicitReadingNavigation=true;const target=document.getElementById('day-'+link.dataset.date);if(!target)return;dateNav.querySelectorAll('a').forEach(a=>a.removeAttribute('aria-current'));link.setAttribute('aria-current','date');history.replaceState(null,'','#'+target.id);reserveScrollRoom(target,76);target.scrollIntoView({block:'start',behavior:'instant'});closeDateNav();if(matchMedia('(max-width:1279px)').matches)dateToggle.focus({preventScroll:true});}));
function reserveScrollRoom(target,desiredTop){
 const main=document.querySelector('.learning-page');
 main.style.paddingBottom='';
 const base=parseFloat(getComputedStyle(main).paddingBottom)||0;
 const needed=window.scrollY+target.getBoundingClientRect().top-desiredTop+window.innerHeight-document.documentElement.scrollHeight;
 if(needed>0)main.style.paddingBottom=(base+Math.ceil(needed))+'px';
}
function changeLanguage(lang,preserve=true){const anchor=preserve?(visibleMessages().find(m=>m.getBoundingClientRect().bottom>20)||visibleMessages().at(-1)):null;const top=anchor?.getBoundingClientRect().top;document.querySelectorAll('[data-lang]').forEach(n=>n.hidden=n.dataset.lang!==lang);document.querySelectorAll('[data-language]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.language===lang)));document.documentElement.lang=lang==='zh'?'zh-CN':'en';updateToolLabels();if(anchor){reserveScrollRoom(anchor,top);window.scrollBy({top:anchor.getBoundingClientRect().top-top,behavior:'instant'});}}
document.querySelectorAll('[data-language]').forEach(b=>b.addEventListener('click',()=>changeLanguage(b.dataset.language)));
async function locateLatest(){await document.fonts.ready;const img=document.querySelector('#sourceTheorem');if(!img.complete)await new Promise(resolve=>{img.addEventListener('load',resolve,{once:true});img.addEventListener('error',resolve,{once:true});});await new Promise(requestAnimationFrame);if(explicitReadingNavigation)return;const requested=location.hash?document.getElementById(location.hash.slice(1)):null;const target=requested&&!requested.hidden?requested:visibleMessages().at(-1);if(target){reserveScrollRoom(target,76);target.scrollIntoView({block:'start',behavior:'instant'});}}
locateLatest();
