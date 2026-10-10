import {paginateOverview} from './proof-overview-model.js?v=20261010-linear-78';
import {drawOverviewWires} from './proof-overview-wires.js?v=20261010-linear-78';
import {english} from './i18n.js?v=20261010-linear-78';
import {graphStatement,statementPanel,escapeHTML,declarationKind,isReferenceCard} from './theorem-statements.js?v=20261010-linear-78';
import {createProofPackages} from './proof-package-model.js?v=20261010-linear-78';

export function installProofWorlds({nodes,select,selected,nodeEditor,theoremTarget}){
  const model=createProofPackages(nodes),panel=document.querySelector('.graph-panel'),viewport=document.querySelector('.graph-scroll');
  const state={target:'lemma',pack:null,mode:'world',catalog:false,page:0,trail:[],reading:null};
  const text=(zh,en)=>english?en:zh;
  const root=document.createElement('section');root.className='proof-worlds';root.setAttribute('aria-label',text('按原稿组织的证明世界','Proof worlds from the manuscript'));
  const bar=document.createElement('nav');bar.className='proof-world-bar';
  const back=document.createElement('button'),home=document.createElement('button'),path=document.createElement('span'),toggle=document.createElement('button');
  for(const b of [back,home,toggle]){b.type='button';b.className='button small';}
  back.dataset.worldBack='';home.dataset.worldHome='';toggle.dataset.worldToggle='';path.className='proof-world-path';bar.append(back,home,path,toggle);panel.prepend(bar);panel.append(root);
  const target=theoremTarget.createCard('world');target.element.classList.add('proof-world-target');
  const canvas=document.createElement('div');canvas.className='proof-world-canvas';
  const scene=document.createElement('div');scene.className='proof-world-scene';
  const wires=document.createElementNS('http://www.w3.org/2000/svg','svg');wires.classList.add('world-wires');wires.setAttribute('aria-hidden','true');
  const deck=document.createElement('div');deck.className='proof-world-deck';
  const reading=document.createElement('div');reading.className='world-reading-heading';canvas.append(reading);
  const tools=document.createElement('div');tools.className='proof-world-tools';
  const previous=document.createElement('button'),next=document.createElement('button'),count=document.createElement('output'),catalog=document.createElement('button');
  for(const b of [previous,next,catalog]){b.type='button';b.className='button small';}tools.append(catalog,previous,count,next);scene.append(wires,deck,target.element);canvas.append(scene);root.append(canvas,tools);
  const slots=['top','left','right','bottom','top-left','bottom-right'];
  let wireFrame=0,focusUntil=0,gesture=null,suppressClickUntil=0;
  const queueWires=()=>{cancelAnimationFrame(wireFrame);wireFrame=requestAnimationFrame(drawWires);};
  function cameraPose(){
    const value=getComputedStyle(scene).transform,m=value==='none'?new DOMMatrixReadOnly():new DOMMatrixReadOnly(value);
    return {x:m.e,y:m.f,scale:m.a};
  }
  function moveCamera(x,y,scale,animate=false){
    scene.style.transition=animate?'':'none';scene.style.transform=`translate(${x}px,${y}px) scale(${scale})`;
    const zoom=document.querySelector('.editor-navigation output');if(zoom&&state.mode==='world')zoom.textContent=`${Math.round(scale*100)}%`;
    queueWires();
  }
  canvas.addEventListener('pointerdown',e=>{
    suppressClickUntil=0;
    if(state.mode!=='world'||e.button!==0||e.target.closest('a,input,select,textarea,summary,button:not(.node)'))return;
    gesture={id:e.pointerId,x:e.clientX,y:e.clientY,pose:cameraPose(),dragging:false};
  });
  canvas.addEventListener('pointermove',e=>{
    if(!gesture||gesture.id!==e.pointerId)return;
    const dx=e.clientX-gesture.x,dy=e.clientY-gesture.y;
    if(!gesture.dragging&&Math.hypot(dx,dy)<5)return;
    if(!gesture.dragging){gesture.dragging=true;canvas.setPointerCapture(e.pointerId);canvas.classList.add('is-panning');}
    e.preventDefault();moveCamera(gesture.pose.x+dx,gesture.pose.y+dy,gesture.pose.scale);
  });
  const finishPan=e=>{
    if(!gesture||gesture.id!==e.pointerId)return;
    if(gesture.dragging){suppressClickUntil=performance.now()+400;if(canvas.hasPointerCapture(e.pointerId))canvas.releasePointerCapture(e.pointerId);}
    gesture=null;canvas.classList.remove('is-panning');
  };
  canvas.addEventListener('pointerup',finishPan);canvas.addEventListener('pointercancel',finishPan);
  canvas.addEventListener('lostpointercapture',finishPan);
  canvas.addEventListener('click',e=>{if(e.detail>0&&performance.now()<suppressClickUntil){e.preventDefault();e.stopImmediatePropagation();}},true);
  canvas.addEventListener('dragstart',e=>e.preventDefault());
  canvas.addEventListener('wheel',e=>{
    if(state.mode!=='world'||e.target.closest('input,select,textarea'))return;
    e.preventDefault();const pose=cameraPose(),box=canvas.getBoundingClientRect();
    const delta=e.deltaY*(e.deltaMode===1?16:e.deltaMode===2?box.height:1),scale=Math.max(.25,Math.min(2.5,pose.scale*Math.exp(-delta*.0015))),ratio=scale/pose.scale;
    const x=e.clientX-box.left,y=e.clientY-box.top;
    moveCamera(x-(x-pose.x)*ratio,y-(y-pose.y)*ratio,scale);
  },{passive:false});
  function drawWires(){
    if(state.mode!=='world')return;
    if(state.pack){wires.innerHTML='';return;}
    if(state.target==='lemma'){drawOverviewWires({scene,wires,deck,target:target.element,model,scale:cameraPose().scale,english,escapeHTML});if(performance.now()<focusUntil)queueWires();return;}
    const screen=scene.getBoundingClientRect(),scale=cameraPose().scale,box={left:0,top:0,width:scene.clientWidth,height:scene.clientHeight};if(!box.width||!box.height)return;
    const localRect=el=>{const r=el.getBoundingClientRect();return {left:(r.left-screen.left)/scale,top:(r.top-screen.top)/scale,right:(r.right-screen.left)/scale,bottom:(r.bottom-screen.top)/scale,width:r.width/scale,height:r.height/scale};};
    const goal=localRect(target.element);
    wires.setAttribute('viewBox',`0 0 ${box.width} ${box.height}`);
    const center={x:goal.left-box.left+goal.width/2,y:goal.top-box.top+goal.height/2};
    let html='<defs><linearGradient id="world-wire-metal" x2="100%"><stop stop-color="#66859e"/><stop offset=".45" stop-color="#cee8f6"/><stop offset="1" stop-color="#638eae"/></linearGradient></defs>';
    for(const shell of deck.querySelectorAll('.proof-package')){
      const card=shell.querySelector('.node'),r=localRect(card),slot=shell.dataset.worldSlot;
      const side='left';
      let a,b,controlA,controlB;
      const x=r.left-box.left+r.width/2,y=r.top-box.top+r.height/2;
      if(side==='top'||side==='bottom'){
        const sign=side==='top'?-1:1;
        a={x,y:side==='top'?r.bottom-box.top+5:r.top-box.top-5};b={x:center.x,y:center.y+sign*(goal.height/2+6)};
        const bend=Math.max(15,Math.abs(a.y-b.y)*.45);controlA={x:a.x,y:a.y-sign*bend};controlB={x:b.x,y:b.y+sign*bend};
      }else{
        const sign=side==='left'?-1:1;
        a={x:side==='left'?r.right-box.left+5:r.left-box.left-5,y};b={x:center.x+sign*(goal.width/2+6),y:center.y};
        const bend=Math.max(15,Math.abs(a.x-b.x)*.45);controlA={x:a.x-sign*bend,y:a.y};controlB={x:b.x+sign*bend,y:b.y};
      }
      const source=card.dataset.worldNode||card.dataset.worldPack,reference=!!card.dataset.worldPack||!!state.pack,reading=reference||state.target==='lemma'||!!originalById.get(state.target)?.overviewSteps;
      const label=reference?text('参考来源；不是新增证明依赖','Reference source; not an added proof dependency'):reading?text('原稿证明模块的阅读路径','Reading path through manuscript proof modules'):text('当前声明的直接前提','Direct premise of the current declaration');
      const d=`M${a.x} ${a.y} C${controlA.x} ${controlA.y},${controlB.x} ${controlB.y},${b.x} ${b.y}`;
      html+=`<g class="world-wire${reference?' source-wire':''}" data-source="${escapeHTML(source)}" data-side="${side}" data-relation="${reading?'reading':'premise'}"><title>${escapeHTML(label)}</title><path class="world-wire-shadow" d="${d}"/><path class="world-wire-body" d="${d}"/><path class="world-wire-shine" d="${d}"/></g>`;
      shell.dataset.connectionSide=side;
      let port=card.querySelector('.world-source-port');if(!port){port=document.createElement('span');port.className='world-source-port';port.setAttribute('aria-hidden','true');card.append(port);}port.dataset.side=side==='top'?'bottom':side==='bottom'?'top':side;
    }
    wires.innerHTML=html;
    if(performance.now()<focusUntil)queueWires();
  }
  // Size the occupied grid, not empty fractional tracks spanning the entire window.
  function layoutDeck(){
    if(state.pack||state.mode!=='world')return;
    const width=canvas.clientWidth,height=canvas.clientHeight,count=deck.querySelectorAll('.proof-package').length;
    if(!width||!height||!count)return;
    const clamp=(n,min,max)=>Math.max(min,Math.min(max,n));
    const xGap=Math.round(clamp(width*.025,18,48)),yGap=Math.round(clamp(height*.035,16,40));
    const goalWidth=Math.round(clamp(width*.27,180,340)),goalGap=Math.round(clamp(width*.035,24,56)),padding=Math.round(clamp(width*.014,12,24));
    const available=Math.max(220,width-goalWidth-goalGap-padding*2);
    const preferred=state.target==='lemma'?3:2;
    const columns=Math.max(1,Math.min(preferred,count,Math.floor((available+xGap)/(230+xGap))));
    const cardWidth=Math.min(280,(available-xGap*(columns-1))/columns),rows=Math.ceil(count/columns);
    const cardHeight=clamp(Math.floor((height-60-(rows-1)*yGap)/rows),140,156);
    root.dataset.compactRows=String(cardHeight<156);
    const deckHeight=rows*cardHeight+(rows-1)*yGap,top=Math.max(36,(height-deckHeight)/2);
    const values={'--world-columns':columns,'--world-rows':rows,'--world-card-width':cardWidth+'px','--world-card-height':cardHeight+'px','--world-x-gap':xGap+'px','--world-y-gap':yGap+'px','--world-deck-width':available+'px','--world-deck-height':deckHeight+'px','--world-deck-top':top+'px','--world-goal-width':goalWidth+'px','--world-goal-gap':goalGap+'px','--world-padding':padding+'px'};
    for(const [name,value] of Object.entries(values))root.style.setProperty(name,String(value));
  }
  new ResizeObserver(()=>{layoutDeck();if(state.reading)focusReading();queueWires();}).observe(canvas);target.element.addEventListener('theoremcardchange',queueWires);
  const originalById=model.byId;
  const catalogOwner=()=>state.pack?'pack:'+state.pack:(model.roots.includes(state.target)?state.target:model.owner.get(state.target));
  const packUses=()=>{const ids=model.closure(state.target);return model.references.filter(p=>p.cards.some(n=>ids.has(n.id)));};
  function proofCard(n){
    const shell=document.createElement('div');shell.className='proof-package';shell.dataset.proofCard=n.id;
    const deps=model.children(n.id); const paperStatus=n.paperProofStatus==='complete'?text('原文引理 · 完整已证','Manuscript lemma · complete'):n.paperProofStatus==='core-proved'?text('原文引理 · 核心已证，接口待补','Manuscript lemma · core proved, interfaces open'):text('原文引理 · 待证','Manuscript lemma · open');shell.dataset.hasCards=String(!!deps.length&&!n.paperCard); if(n.paperIndex){shell.dataset.paperIndex=n.paperIndex;shell.dataset.paperProofStatus=n.paperProofStatus;}
    const card=document.createElement('button');card.type='button';card.className='node '+n.status;card.dataset.worldNode=n.id;card.setAttribute('aria-label',n.title+' · '+text('左击阅读信息，右击进入证明','Click to read; right-click to enter the proof'));
    card.setAttribute('aria-pressed',String(selected()===n.id));
    card.innerHTML=`<b class="node-heading">${escapeHTML(n.title)}</b><div class="node-proposition">${graphStatement(n,english)}</div><span class="world-package-caption">${n.paperIndex?paperStatus:declarationKind(n)==='definition'?text('定义 / 构造','DEFINITION / CONSTRUCTION'):text('证明模块','PROOF MODULE')} · ${deps.length} ${text('步骤','steps')}</span><small class="${n.status}">${escapeHTML(n.status==='conditional'?text('✓ Lean · 辅助定理','✓ Lean · auxiliary theorem'):n.status==='done'?text('✓ Lean 已验证','✓ Verified by Lean'):text('待补证明','Open proof'))}</small><span class="node-input-socket" aria-hidden="true"></span><span class="node-output-socket" aria-hidden="true"></span>`;
    card.onclick=()=>inspectNode(n.id);card.oncontextmenu=e=>{e.preventDefault();enter(n.id,null,card);};
    card.onkeydown=e=>{if(e.key==='ContextMenu'||(e.shiftKey&&e.key==='F10')){e.preventDefault();enter(n.id);}};
    shell.append(card);return shell;
  }
  function referenceCard(p){
    const shell=document.createElement('div');shell.className='proof-package reference-package';shell.dataset.hasCards='true';
    const card=document.createElement('button');card.type='button';card.className='node reference-pack-card';card.dataset.worldPack=p.id;card.setAttribute('aria-label',p.name[english?1:0]+' · '+p.cards.length+' '+text('张卡片','cards'));
    card.innerHTML=`<b class="node-heading"><span class="world-pack-mark">${p.mark}</span>${escapeHTML(p.name[english?1:0])}</b><div class="node-proposition"><div><b>${text('参考来源','REFERENCE SOURCE')}</b><span>${escapeHTML(p.reference[english?1:0])}</span></div><div><b>${text('包内定理与构造','THEOREMS AND CONSTRUCTIONS')}</b><span>${p.cards.length} ${text('张已编入的卡片','indexed cards')}</span></div></div><span class="node-output-socket" aria-hidden="true"></span><span class="world-package-caption">${text('阅读来源，不是新增假设','Reading source, not an added hypothesis')}</span>`;
    card.title=text('左击阅读卡包信息；右击打开卡包（Shift＋F10）','Click for pack information; right-click to open pack (Shift+F10)');
    card.onclick=()=>inspectPack(p.id);card.oncontextmenu=e=>{e.preventDefault();enter(state.target,p.id);};
    card.onkeydown=e=>{if(e.key==='ContextMenu'||(e.shiftKey&&e.key==='F10')){e.preventDefault();enter(state.target,p.id);}};shell.append(card);return shell;
  }
  const detail=document.querySelector('#detail');
  const closeInfo=document.createElement('button');closeInfo.type='button';closeInfo.className='world-detail-close';closeInfo.textContent='×';closeInfo.hidden=true;
  const packInfo=document.createElement('section');packInfo.className='world-pack-info';packInfo.hidden=true;detail.prepend(closeInfo,packInfo);
  closeInfo.onclick=closeReading;
  document.addEventListener('keydown',e=>{if(e.key==='Escape'&&state.reading)closeReading();});
  target.element.addEventListener('click',e=>{if(!e.target.closest('button,a,summary'))inspectNode(state.target);});
  function resetCardFocus(){
    delete target.element.dataset.readingFocus;
    for(const shell of deck.querySelectorAll('.proof-package')){delete shell.dataset.readingFocus;shell.querySelector('.node').setAttribute('aria-pressed',String(shell.querySelector('.node').dataset.worldNode===selected()));}
  }
  function closeReading(){
    state.reading=null;document.body.classList.remove('world-inspector-open','inspector-open');delete detail.dataset.worldPack;packInfo.hidden=true;closeInfo.hidden=true;resetCardFocus();const pose=cameraPose();moveCamera(0,0,pose.scale,true);
  }
  function showInformation(){
    document.body.classList.add('world-inspector-open');closeInfo.hidden=false;closeInfo.setAttribute('aria-label',text('关闭信息面板','Close information panel'));closeInfo.title=closeInfo.getAttribute('aria-label');detail.scrollTop=0;
  }
  function focusReading(){
    if(!state.reading||state.mode!=='world')return;resetCardFocus();
    let card=state.reading.pack?deck.querySelector(`[data-world-pack="${state.reading.pack}"]`):deck.querySelector(`[data-world-node="${state.reading.node}"]`);
    if(!card&&state.reading.node){const owner=model.owner.get(state.reading.node);if(owner?.startsWith('pack:'))card=deck.querySelector(`[data-world-pack="${owner.slice(5)}"]`);}
    if(!card&&state.reading.node===state.target&&!state.pack)card=target.element;
    if(!card)return;
    const gold=card===target.element,shell=gold?card:card.closest('.proof-package'),box=canvas.getBoundingClientRect(),r=card.getBoundingClientRect(),aside=detail.getBoundingClientRect();
    // Move the whole scene; cards and wires retain their relative positions.
    const pose=cameraPose();
    const available=Math.max(r.width,aside.left-box.left-32),cx=box.left+available*.78,cy=box.top+box.height/2;
    const dx=Math.max(box.left+8,Math.min(cx-r.width/2,aside.left-r.width-20))-r.left+pose.x,dy=cy-r.height/2-r.top+pose.y;
    shell.dataset.readingFocus='true';if(!gold)card.setAttribute('aria-pressed','true');
    moveCamera(Math.round(dx),Math.round(dy),pose.scale,true);
    focusUntil=performance.now()+280;queueWires();
  }
  function inspectNode(id){
    if(!originalById.has(id))return;
    delete detail.dataset.worldPack;packInfo.hidden=true;state.reading={node:id};select(id);showInformation();
    const url=new URL(location);url.searchParams.set('world',state.target);history.replaceState(history.state,'',url);
    requestAnimationFrame(focusReading);
  }
  function packInformation(id){
    const p=model.packFor(id);if(!p)return;
    detail.dataset.worldPack=id;packInfo.hidden=false;
    const chain=model.closure(state.target),used=p.cards.filter(n=>chain.has(n.id));
    const list=cards=>cards.map(n=>`<button type="button" class="dep-link" data-inspect-node="${escapeHTML(n.id)}">${escapeHTML(n.title)}<span>${['done','conditional'].includes(n.status)?text('✓ Lean 已验证','✓ Lean verified'):text('待补证明','Open proof')}</span></button>`).join('');
    packInfo.innerHTML=`<p class="world-pack-kind">${text('参考卡包','REFERENCE PACK')}</p><h2>${escapeHTML(p.name[english?1:0])}</h2><p>${escapeHTML(p.reference[english?1:0])}</p><p>${p.cards.length} ${text('张定理与构造卡片','theorem and construction cards')}</p><h3>${text('当前证明引用','Used in the current proof')}</h3>${used.length?list(used):`<p>${text('此模块没有引用该包中的卡片。','This module uses no cards from this pack.')}</p>`}<h3>${text('包内全部卡片','All cards in this pack')}</h3>${list(p.cards)}`;
    packInfo.querySelectorAll('[data-inspect-node]').forEach(button=>button.onclick=()=>inspectNode(button.dataset.inspectNode));
  }
  function inspectPack(id){
    if(!model.packFor(id))return;state.reading={pack:id};packInformation(id);showInformation();requestAnimationFrame(focusReading);
  }
  function updatePath(){
    back.disabled=!state.trail.length&&state.mode==='world';back.textContent=text('← 返回','← Back');home.innerHTML='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" aria-hidden="true"><path d="m3 10 9-7 9 7M5 9v11h5v-6h4v6h5V9"/></svg>';home.setAttribute('aria-label',text('返回主证明','Return to the main proof'));home.title=home.getAttribute('aria-label');toggle.textContent=state.mode==='graph'?text('卡片模块','Proof modules'):text('连接图','Connections');
    const labels=[text('原稿 · Linearity Theorem','Manuscript · Linearity Theorem'),...state.trail.filter(s=>s.target!=='lemma'||s.pack).map(s=>s.pack?model.packFor(s.pack)?.name[english?1:0]:originalById.get(s.target)?.title),state.target==='lemma'?null:originalById.get(state.target)?.title,state.pack?model.packFor(state.pack)?.name[english?1:0]:null].filter(Boolean);
    path.textContent=labels.join(' / ');path.title=path.textContent;
    document.body.classList.toggle('proof-world-mode',state.mode==='world');document.body.classList.toggle('proof-graph-mode',state.mode==='graph');root.hidden=state.mode!=='world';viewport.hidden=state.mode==='world';
    if(state.mode==='world'){const zoom=document.querySelector('.editor-navigation output');if(zoom)zoom.textContent=`${Math.round(cameraPose().scale*100)}%`;}
  }
  function render(){
    root.setAttribute('aria-label',text('按原稿组织的证明世界','Proof worlds from the manuscript'));
    updatePath();target.setTarget(originalById.get(state.target));target.element.dataset.worldTarget=state.target;
    const isRoot=state.target==='lemma'&&!state.pack;let members;
    root.dataset.mainProof=String(isRoot);target.element.hidden=!!state.pack;
    root.dataset.referenceWorld=state.pack||'';
    canvas.setAttribute('aria-label',state.pack?text('参考卡牌：从上到下展开','Reference cards: vertical fan'):isRoot?text('PDF 原稿证明脉络与主定理','PDF proof path and main theorem'):text('证明步骤与目标','Proof steps and target'));
    if(state.pack)members=model.members('pack:'+state.pack);
    else if(state.catalog)members=model.members(catalogOwner()||state.target).filter(n=>n.id!==state.target);
    else members=(isRoot?model.roots:model.children(state.target)).map(id=>originalById.get(id)).filter(Boolean);
    const refs=state.pack?[]:isRoot?model.references:packUses();
    // References already have their own pack; they appear once as a pack cover.
    if(!state.pack)members=members.filter(n=>!model.owner.get(n.id)?.startsWith('pack:'));
    const pageSize=state.pack?Math.max(1,members.length):isRoot?9:6,items=[...members.map(n=>({n})),...refs.map(p=>({p}))];
    const overview=isRoot&&!state.catalog?paginateOverview(items,state.page,pageSize):null;
    const pages=overview?.pages||Math.max(1,Math.ceil(items.length/pageSize));state.page=overview?.page??Math.min(state.page,pages-1);
    const shown=overview?.shown||items.slice(state.page*pageSize,(state.page+1)*pageSize);
    root.dataset.pinnedLemmaCount=String(overview?.pinned||0);
    deck.replaceChildren(...shown.map(item=>item.n?proofCard(item.n):referenceCard(item.p)));
    target.element.querySelectorAll('.theorem-port').forEach(port=>port.hidden=!!state.pack||!items.length||port.dataset.side!=='left');
    [...deck.children].forEach((card,i)=>{card.dataset.worldSlot=slots[i];card.style.setProperty('--fan-order',i);});layoutDeck();queueWires();
    if(!items.length){const note=document.createElement('div');note.className='world-leaf';note.innerHTML=`<p>${text('这个声明没有其他项目卡片作为前提。','This declaration has no other project-card prerequisites.')}</p>`;const evidence=document.createElement('button');evidence.type='button';evidence.className='button';evidence.textContent=text('查看 Lean 声明与源码','Read the Lean declaration and source');evidence.onclick=()=>openGraph(state.target);note.append(evidence);deck.append(note);}
    reading.textContent=state.pack?model.packFor(state.pack).name[english?1:0]+text(' · 纵向卡牌',' · Vertical cards'):isRoot?text('线性定理 · 形式化进度','Linearity Theorem · formalization progress'):text('当前目标的证明步骤','Proof steps for the current goal');
    root.dataset.worldTarget=state.target;root.dataset.referenceWorld=state.pack||'';root.dataset.catalog=String(state.catalog);
    previous.textContent='←';next.textContent='→';previous.setAttribute('aria-label',text('上一组卡片','Previous cards'));next.setAttribute('aria-label',text('下一组卡片','Next cards'));previous.disabled=state.page===0;next.disabled=state.page===pages-1;previous.hidden=next.hidden=pages===1;
    count.textContent=overview?.pinned?`${overview.pinned} ${text('引理','lemmas')} · ${overview.start}–${overview.end} / ${overview.total} ${text('辅助卡片','support cards')}`:items.length?`${state.page*pageSize+1}–${Math.min(items.length,(state.page+1)*pageSize)} / ${items.length}`:'';
    catalog.hidden=!!state.pack||!model.members(catalogOwner()||state.target).some(n=>n.id!==state.target);catalog.textContent=state.catalog?text('当前证明步骤','Current proof steps'):text('模块全部卡片','All module cards');catalog.setAttribute('aria-pressed',String(state.catalog));
    if(state.reading&&state.mode==='world'){showInformation();if(state.reading.pack)packInformation(state.reading.pack);requestAnimationFrame(focusReading);}
    if(state.mode==='graph')nodeEditor.setWorldContext({target:originalById.get(state.target),allowed:new Set([...model.closure(state.target),...model.closure(selected())]),reference:isReferenceCard(originalById.get(selected()))});
    document.dispatchEvent(new Event('proofworldrender'));
  }
  function save(){const url=new URL(location);if(state.mode==='world'&&!state.pack)url.hash='node='+state.target;if(state.target==='lemma')url.searchParams.delete('world');else url.searchParams.set('world',state.target);if(state.pack)url.searchParams.set('pack',state.pack);else url.searchParams.delete('pack');history.replaceState(history.state,'',url);}
  async function enter(id,pack=null){
    if(!originalById.has(id))return;const priorCamera=cameraPose();closeReading();
    state.trail.push({target:state.target,pack:state.pack,mode:state.mode,catalog:state.catalog,page:state.page,camera:state.mode==='graph'?nodeEditor.getCamera():null,worldCamera:priorCamera});
    Object.assign(state,{target:id,pack,mode:'world',catalog:false,page:0});moveCamera(0,0,1);render();save();
  }
  function openGraph(id=state.target){
    if(!originalById.has(id))return;closeReading();const fromWorld=state.mode==='world';state.mode='graph';state.pack=null;updatePath();
    nodeEditor.setWorldContext({target:originalById.get(state.target),allowed:new Set([...model.closure(state.target),...model.closure(id)]),reference:isReferenceCard(originalById.get(id))});
    select(id);requestAnimationFrame(()=>{nodeEditor.show();if(fromWorld)nodeEditor.frame('selected');});save();
  }
  function restore(){
    closeReading();
    if(state.mode==='graph'){state.mode='world';render();save();return;}
    const prior=state.trail.pop();if(!prior)return;Object.assign(state,prior);if(prior.worldCamera)moveCamera(prior.worldCamera.x,prior.worldCamera.y,prior.worldCamera.scale);render();if(prior.mode==='graph')nodeEditor.restoreCamera(prior.camera);save();
  }
  back.onclick=restore;home.onclick=()=>{closeReading();moveCamera(0,0,1);Object.assign(state,{target:'lemma',pack:null,mode:'world',catalog:false,page:0,trail:[]});render();save();};toggle.onclick=()=>state.mode==='world'?openGraph():restore();catalog.onclick=()=>{state.catalog=!state.catalog;state.page=0;render();};previous.onclick=()=>{state.page--;render();};next.onclick=()=>{state.page++;render();};
  document.querySelector('#graph').addEventListener('contextmenu',e=>{const card=e.target.closest('.node[data-node]');if(card){e.preventDefault();enter(card.dataset.node,null,card);}});
  document.addEventListener('referencecardrequest',e=>{const id=e.detail;if(originalById.has(id)){const source=model.owner.get(id);if(source?.startsWith('pack:'))enter(state.target,source.slice(5)).then(()=>{state.page=Math.floor(model.members(source).findIndex(n=>n.id===id)/6);render();});}});
  document.addEventListener('click',e=>{const b=e.target.closest('[data-select]');if(!b)return;if(state.mode==='world'){e.preventDefault();inspectNode(b.dataset.select);}});
  window.addEventListener('languagechange',render);
  document.querySelector('#editorSelect')?.addEventListener('change',e=>state.mode==='world'?inspectNode(e.target.value):openGraph(e.target.value));
  document.querySelector('#scope')?.addEventListener('change',()=>{if(state.mode==='world')openGraph();});
  document.addEventListener('proofgraphtoolrequest',e=>{if(state.mode==='world'){openGraph();requestAnimationFrame(()=>e.detail?.());}else e.detail?.();});
  const params=new URLSearchParams(location.search),initial=params.get('world'),initialPack=params.get('pack');if(originalById.has(initial))state.target=initial;if(model.packFor(initialPack))state.pack=initialPack;
  render();
  // Deep links to old cards remain valid; they are initially inside the matching module.
  if(!params.has('world')&&selected()!=='lemma'){const owner=model.owner.get(selected());if(owner?.startsWith('pack:'))state.pack=owner.slice(5);else if(owner)state.target=owner;render();}
  installBottomTools();
  document.querySelectorAll('.editor-navigation button').forEach(button=>{
    const fallback=button.onclick;
    button.onclick=()=>{
      if(state.mode!=='world'){fallback?.();return;}
      const pose=cameraPose();
      if(button.dataset.nodeZoom){const k=button.dataset.nodeZoom==='in'?1.2:1/1.2,scale=Math.max(.25,Math.min(2.5,pose.scale*k)),x=canvas.clientWidth/2,y=canvas.clientHeight/2;moveCamera(x-(x-pose.x)*scale/pose.scale,y-(y-pose.y)*scale/pose.scale,scale);}
      else if(button.dataset.frame==='selected'&&state.reading)focusReading();
      else if(button.dataset.frame==='theorem')inspectNode(state.target);
      else moveCamera(0,0,1);
    };
  });
  return {state,model,openGraph,enter,render};
}

function installBottomTools(){
  const footer=document.querySelector('.atlas-statusbar'),row=document.createElement('nav');row.className='proof-bottom-tools';row.setAttribute('aria-label',english?'Proof workspace tools':'证明工作区工具');
  const modules=document.querySelector('.module-navigation'),dock=document.querySelector('.atlas-dock'),camera=document.querySelector('.editor-navigation'),nodeHistory=document.querySelector('.node-history'),inspector=document.querySelector('.workspace>.inspector-toggle');
  for(const el of [modules,nodeHistory,dock,camera,inspector])if(el)row.append(el);
  footer.prepend(row);
  const moduleIcons={atlas:'<circle cx="5" cy="6" r="2"/><circle cx="19" cy="6" r="2"/><circle cx="12" cy="18" r="2"/><path d="m6 8 5 8m7-8-5 8"/>',original:'<path d="M12 5C8 3 5 3 2 4v15c4-1 6-1 10 1 4-2 6-2 10-1V4c-3-1-6-1-10 1zm0 0v15"/>',evidence:'<path d="M6 3h9l3 3v15H6zM15 3v4h4m-10 7 2 2 4-5"/>'};
  for(const a of modules.querySelectorAll('a')){const id=a.hash.slice(1),label=a.textContent.trim();a.setAttribute('aria-label',label);a.title=label;a.innerHTML=`<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${moduleIcons[id]}</svg><span class="bottom-module-label">${escapeHTML(label)}</span>`;}
  const cameraIcons={all:'<path d="M8 3H3v5m13-5h5v5M3 16v5h5m13-5v5h-5"/>',selected:'<circle cx="12" cy="12" r="5"/><path d="M12 2v4m0 12v4M2 12h4m12 0h4"/>',theorem:'<path d="m3 7 4 5 5-8 5 8 4-5-2 13H5z"/>',in:'<path d="M5 12h14M12 5v14"/>',out:'<path d="M5 12h14"/>'};
  for(const b of camera.querySelectorAll('button')){const key=b.dataset.frame||b.dataset.nodeZoom,label=b.title||b.getAttribute('aria-label')||b.textContent.trim();b.setAttribute('aria-label',label);b.title=label;b.innerHTML=`<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" aria-hidden="true">${cameraIcons[key]}</svg>`;}
  for(const b of camera.querySelectorAll('button')){const action=b.onclick;b.onclick=()=>document.dispatchEvent(new CustomEvent('proofgraphtoolrequest',{detail:action}));}
  if(inspector){const action=inspector.onclick;inspector.onclick=()=>document.dispatchEvent(new CustomEvent('proofgraphtoolrequest',{detail:action}));}
  for(const b of dock.querySelectorAll('button')){const caption=b.querySelector('.dock-caption')?.textContent;b.setAttribute('aria-label',caption||'2D');if(!b.title)b.title=caption||'2D';}
  const expand=document.querySelector('#expandGraph');expand.title=expand.getAttribute('title')||'Expand atlas';expand.setAttribute('aria-label',expand.title);
  const updateLabels=()=>{
    row.setAttribute('aria-label',english?'Proof workspace tools':'证明工作区工具');
    const names={atlas:['证明图谱','Proof atlas'],original:['原始证明','Original proof'],evidence:['验证记录','Verification evidence']};
    for(const a of modules.querySelectorAll('a')){const label=names[a.hash.slice(1)]?.[english?1:0];if(label){a.title=label;a.setAttribute('aria-label',label);a.querySelector('.bottom-module-label').textContent=label;}}
    const frames={all:['显示全部','Frame all'],selected:['聚焦所选','Frame selected'],theorem:['主定理','Theorem'],in:['放大','Zoom in'],out:['缩小','Zoom out']};
    for(const b of camera.querySelectorAll('button')){const label=frames[b.dataset.frame||b.dataset.nodeZoom]?.[english?1:0];if(label){b.title=label;b.setAttribute('aria-label',label);}}
    for(const b of dock.querySelectorAll('[data-view]')){const label=b.dataset.view==='2d'?(english?'2D map':'2D 平面'):(english?'3D paused':'3D 暂停');b.setAttribute('aria-label',label);}
    expand.setAttribute('aria-label',english?'Expand atlas':'展开图谱');
  };
  updateLabels();window.addEventListener('languagechange',updateLabels);
}
