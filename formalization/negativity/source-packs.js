import {declarationKind,handStatement,isReferenceCard,escapeHTML} from './theorem-statements.js?v=20261004-statements-45';
import {buildSourcePacks,sourcePackFor} from './source-pack-catalog.js?v=20261004-packs-43';
import {english} from './i18n.js?v=20261004-formal-42';

export function installSourcePacks({viewport,nodes,select,selected}){
  const packs=buildSourcePacks(nodes),byId=new Map(nodes.map(n=>[n.id,n]));
  let active=isReferenceCard(byId.get(selected()))?sourcePackFor(byId.get(selected())):null,page=0,query='',pageSize=5;
  const root=document.createElement('section');root.className='source-packs';root.dataset.open='false';
  const tray=document.createElement('div');tray.className='source-pack-tray';tray.hidden=true;tray.id='sourcePackTray';
  const header=document.createElement('div');header.className='source-pack-header';
  const heading=document.createElement('strong'),close=document.createElement('button');close.type='button';close.className='pack-close';close.textContent='×';
  header.append(heading,close);
  const reference=document.createElement('div');reference.className='source-pack-reference';
  const tools=document.createElement('div');tools.className='source-pack-tools';
  const search=document.createElement('input');search.type='search';search.className='source-pack-search';
  const previous=document.createElement('button'),next=document.createElement('button'),count=document.createElement('output');
  previous.type=next.type='button';previous.textContent='‹';next.textContent='›';tools.append(search,previous,count,next);
  const hand=document.createElement('div');hand.className='source-pack-hand';
  const note=document.createElement('p');note.className='source-pack-note';
  tray.append(header,reference,tools,hand,note);
  const shelf=document.createElement('div');shelf.className='source-pack-shelf';
  const title=document.createElement('span');title.className='source-pack-shelf-title';
  const buttons=document.createElement('div');buttons.className='source-pack-buttons';
  const locate=document.createElement('button');locate.type='button';locate.className='source-pack-locate';
  const shelfHeading=document.createElement('div');shelfHeading.className='source-pack-shelf-heading';shelfHeading.append(title,locate);
  shelf.append(shelfHeading,buttons);root.append(tray,shelf);viewport.parentElement.append(root);

  const text=pair=>pair[english?1:0];
  const btns=new Map();
  for(const p of packs){
    const b=document.createElement('button');b.type='button';b.className='source-pack-deck';b.dataset.pack=p.id;b.style.setProperty('--pack-ink',p.color);b.setAttribute('aria-controls',tray.id);
    const mark=document.createElement('span');mark.className='pack-mark';mark.textContent=p.mark;
    const label=document.createElement('b'),size=document.createElement('small');size.textContent=p.cards.length;
    b.append(mark,label,size);b.onclick=()=>{active=active===p.id?null:p.id;page=0;query='';search.value='';render();};
    buttons.append(b);btns.set(p.id,{b,label});
  }
  function relevant(){const ids=new Set();function walk(id){if(ids.has(id))return;ids.add(id);byId.get(id)?.deps.forEach(walk);}walk(selected());return ids;}
  function cardButton(n,i,total,ids){
    const b=document.createElement('button');b.type='button';b.className='source-hand-card';b.dataset.packNode=n.id;
    b.style.setProperty('--card-index',i);b.style.setProperty('--card-mid',(total-1)/2);b.style.zIndex=String(i+1);
    b.setAttribute('aria-pressed',String(n.id===selected()));b.dataset.related=String(ids.has(n.id));
    const corner=document.createElement('span');corner.className='hand-card-corner';corner.innerHTML=`<span>${String(page*pageSize+i+1).padStart(2,'0')}</span><span class="hand-card-kind">${declarationKind(n)==='definition'?(english?'Construction':'定义 / 构造'):(english?'Theorem':'定理')}</span>`;
    const title=document.createElement('b');title.className='hand-card-title';title.textContent=n.title;
    const statement=document.createElement('span');statement.className='hand-card-statement';statement.innerHTML=handStatement(n,english);
    const declaration=document.createElement('code');declaration.className='hand-card-declaration';declaration.textContent=n.decl;declaration.title=n.decl;
    const footer=document.createElement('span');footer.className='hand-card-footer';
    const verified=['done','conditional'].includes(n.status);
    footer.textContent=(verified?'✓ Lean': '?')+' · '+(n.id===selected()?(english?'Selected':'当前卡片'):ids.has(n.id)?(english?'On this proof path':'当前证明路径'):(english?'Explore':'点开查看'));
    b.title=n.title+'\n'+n.decl+'\n'+(n.statement||'');b.setAttribute('aria-label',n.title+' · '+(verified?(english?'Lean verified':'Lean 已验证'):(english?'Open input':'待补输入')));
    b.append(corner,title,declaration,statement,footer);b.onclick=()=>{select(n.id);if(!isReferenceCard(n))active=null;render();};
    b.onkeydown=e=>{if(e.key==='ArrowLeft'||e.key==='ArrowRight'){e.preventDefault();const all=[...hand.querySelectorAll('button')];all[(i+(e.key==='ArrowRight'?1:-1)+all.length)%all.length].focus();}};
    return b;
  }
  function render(){
    root.dataset.open=String(!!active);tray.hidden=!active;title.textContent=english?'REFERENCE PACKS':'参考卡包';
    root.setAttribute('aria-label',english?'Reference card packs':'数学参考卡包');
    const currentPack=sourcePackFor(byId.get(selected()));
    locate.textContent=english?'Current card ↗':'当前卡片 ↗';locate.title=text(packs.find(p=>p.id===currentPack).name);
    for(const p of packs){const {b,label}=btns.get(p.id);label.textContent=text(p.name);b.dataset.current=String(p.id===currentPack);b.setAttribute('aria-expanded',String(active===p.id));b.setAttribute('aria-pressed',String(active===p.id));b.title=text(p.description);}
    if(!active)return;
    const p=packs.find(p=>p.id===active),filtered=p.cards.filter(n=>!query||[n.title,n.statement,n.file,n.decl].join(' ').toLocaleLowerCase().includes(query));
    page=Math.min(page,Math.max(0,Math.ceil(filtered.length/pageSize)-1));const visible=filtered.slice(page*pageSize,(page+1)*pageSize),ids=relevant();
    heading.textContent=text(p.name);reference.replaceChildren();
    const ref=p.url?document.createElement('a'):document.createElement('span');ref.textContent=text(p.reference);if(p.url){ref.href=p.url;ref.target='_blank';ref.rel='noopener';}reference.append(ref);const contents=document.createElement('span');contents.className='pack-contents';const theoremCount=p.cards.filter(n=>declarationKind(n)==='theorem').length,definitionCount=p.cards.length-theoremCount;contents.textContent=english?`${theoremCount} theorems${definitionCount?` · ${definitionCount} constructions`:''}`:`${theoremCount} 个定理${definitionCount?` · ${definitionCount} 个构造`:''}`;reference.append(contents);
    reference.title=text(p.description);search.placeholder=english?'Find a card…':'查找卡片…';search.setAttribute('aria-label',english?'Search this pack':'搜索当前卡包');
    close.setAttribute('aria-label',english?'Fold cards':'收起手牌');previous.setAttribute('aria-label',english?'Previous hand':'上一组手牌');next.setAttribute('aria-label',english?'Next hand':'下一组手牌');
    previous.disabled=page===0;next.disabled=(page+1)*pageSize>=filtered.length;count.textContent=filtered.length?`${page*pageSize+1}–${page*pageSize+visible.length} / ${filtered.length}`:'0';
    hand.replaceChildren(...visible.map((n,i)=>cardButton(n,i,visible.length,ids)));
    if(!visible.length){const empty=document.createElement('span');empty.className='pack-empty';empty.textContent=english?'No matching cards':'没有匹配的卡片';hand.append(empty);}
    note.textContent=english?'Each card names its theorem and exact Lean declaration.':'每张卡片明确标注定理与对应的 Lean 声明';
  }
  close.onclick=()=>{const prior=active;active=null;render();btns.get(prior)?.b.focus();};
  locate.onclick=()=>{active=sourcePackFor(byId.get(selected()));query='';search.value='';page=Math.floor(packs.find(p=>p.id===active).cards.findIndex(n=>n.id===selected())/pageSize);render();};
  previous.onclick=()=>{page--;render();};next.onclick=()=>{page++;render();};search.oninput=()=>{query=search.value.toLocaleLowerCase();page=0;render();};
  root.addEventListener('keydown',e=>{e.stopPropagation();if(e.key==='Escape'){e.preventDefault();close.click();}});
  for(const event of ['pointerdown','wheel'])root.addEventListener(event,e=>e.stopPropagation());
  const resize=new ResizeObserver(()=>{const size=viewport.clientWidth<520?3:5;if(size!==pageSize){pageSize=size;page=0;render();}});resize.observe(viewport);
  function openCard(id){const n=byId.get(id);if(!n)return;active=sourcePackFor(n);query='';search.value='';page=Math.floor(packs.find(p=>p.id===active).cards.findIndex(c=>c.id===id)/pageSize);render();}
  document.addEventListener('referencecardrequest',e=>openCard(e.detail));
  if(active)page=Math.floor(packs.find(p=>p.id===active).cards.findIndex(n=>n.id===selected())/pageSize);
  render();return {refreshLanguage:render,selectionChanged(){if(isReferenceCard(byId.get(selected())))openCard(selected());else render();},openCard};
}
