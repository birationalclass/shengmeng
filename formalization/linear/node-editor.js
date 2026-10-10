import {isReferenceCard,packLabel,escapeHTML,graphStatement} from './theorem-statements.js?v=20261011-linear-86';
import {recordAtlasRender,recordAtlasLayout} from './performance.js?v=20261011-linear-86';
import {visibleProofIds,compactProofLayout} from './proof-layout.js?v=20261011-linear-86';

import {t,english} from './i18n.js?v=20261011-linear-86';
// Viewer-only node editor: sockets and links always use the curated proof DAG.
export function createNodeEditor({viewport,graph,svg,nodes,select,selected,theoremTarget}) {
  const byId=new Map(nodes.map(n=>[n.id,n]));let layout=new Map(),factor=1,entries=[],revision=0,worldContext=null;
  const cards=new Map([...graph.querySelectorAll('.node')].map(b=>[b.dataset.node,b])),scopePicker=document.querySelector('#scope');
  let diagramSelection=isReferenceCard(byId.get(selected()))?'lemma':selected();
  const referenceNotice=document.createElement('div');referenceNotice.className='reference-view-note';referenceNotice.hidden=true;viewport.append(referenceNotice);
  const focusId=()=>worldContext?.reference?selected():isReferenceCard(byId.get(selected()))?diagramSelection:selected();
  let viewWidth=viewport.clientWidth,viewHeight=viewport.clientHeight,renderFrame=0,detail='full';
  const theoremCard=theoremTarget.createCard('2d');graph.append(theoremCard.element);let theoremBox;
  function buildLayout(){
    const start=performance.now();factor=parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--node-base-font'))/16||1.125;
    const scope=scopePicker.value;let ids=visibleProofIds(nodes,focusId(),scope,!!worldContext?.reference);if(worldContext?.allowed)ids=new Set([...ids].filter(id=>worldContext.allowed.has(id)));ids.add(focusId());layout=compactProofLayout(nodes,ids,factor,scope==='direct'?3:5,{selected:focusId()});revision++;
    entries=[...layout].map(([id,p])=>({id,p,b:cards.get(id)}));
    for(const [id,b] of cards)b.hidden=!ids.has(id);
    for(const {p,b} of entries){b.classList.toggle('base-card',!!p.base);b.classList.toggle('compact-input',!!p.compact);b.dataset.baseInput=String(!!p.base);b.style.zIndex='2';}
    theoremBox=theoremCard.layout(layout,factor);recordAtlasLayout(start);
  }
  buildLayout();
  graph.querySelectorAll('.column-label').forEach(e=>e.remove());
  nodes.forEach(n=>{const p=layout.get(n.id)||{x:0,y:0,h:150*factor},b=cards.get(n.id);b.style.left=p.x+'px';b.style.top=p.y+'px';b.style.height=p.h+'px';b.style.setProperty('--node-x',p.x+'px');b.style.setProperty('--node-y',p.y+'px');b.innerHTML='';const heading=document.createElement('b');heading.className='node-heading';heading.textContent=n.title;heading.title=n.title;b.append(heading);const proposition=document.createElement('div');proposition.className='node-proposition';proposition.dataset.statementCard=n.id;proposition.innerHTML=graphStatement(n,english);b.append(proposition);const sockets=document.createElement('div');sockets.className='node-sockets';
    if(!n.deps.length){const row=document.createElement('span');row.className='node-input empty-input';row.textContent='';sockets.append(row);}n.deps.forEach(id=>{const row=document.createElement('span');row.className='node-input';row.dataset.premise=id;const dependency=byId.get(id);row.title=dependency.title;if(isReferenceCard(dependency)){row.classList.add('reference-input');row.setAttribute('role','link');row.tabIndex=0;row.innerHTML=`<span class="reference-pack-tag">${escapeHTML(packLabel(dependency,english))}</span>${escapeHTML(dependency.title)}`;row.onclick=e=>{e.stopPropagation();select(id);sourcePacks.openCard(id);};row.onkeydown=e=>{if(['Enter',' '].includes(e.key)){e.preventDefault();e.stopPropagation();row.click();}};}else row.textContent=dependency.title;sockets.append(row);});b.append(sockets);const output=document.createElement('span');output.className='node-output';output.textContent=t('结论');b.append(output);const status=document.createElement('small');status.className=n.status;status.textContent=t(({done:'✓ Lean 已验证',conditional:'✓ Lean 已验证 · 辅助定理',assumption:'? 暂作假设',pending:'○ 待完成目标'})[n.status]);b.append(status);const rel=document.createElement('span');rel.className='relation-tag';b.append(rel);const summary=document.createElement('span');summary.className='node-summary';summary.textContent=n.deps.length?(english?n.deps.length+(n.deps.length===1?' premise':' premises'):n.deps.length+' 个前提'):(english?'Source card':'来源卡片');b.append(summary);});
  // Half-round ports sit outside the card; wires meet the outer arc, not the text.
  nodes.forEach(n=>{const b=cards.get(n.id);n.deps.forEach((id,i)=>{const inputPort=document.createElement('span');inputPort.className='node-input-socket'+(isReferenceCard(byId.get(id))?' reference-port':'');inputPort.setAttribute('aria-hidden','true');inputPort.dataset.premise=id;if(i===0)inputPort.dataset.first='';inputPort.style.setProperty('--socket-y',(168+22*i)+'px');b.append(inputPort);});const outputPort=document.createElement('span');outputPort.className='node-output-socket';outputPort.setAttribute('aria-hidden','true');b.append(outputPort);});
  const sourcePacks={selectionChanged(){},refreshLanguage(){},openCard(id){document.dispatchEvent(new CustomEvent('referencecardrequest',{detail:id}));}};
  const ns='http://www.w3.org/2000/svg',wires=document.createElementNS(ns,'g'),links=[];
  const metalDefs=document.createElementNS(ns,'defs');
  metalDefs.innerHTML='<linearGradient id="atlas-wire-metal" gradientUnits="userSpaceOnUse" x2="480" spreadMethod="reflect"><stop stop-color="#6b879d"/><stop offset=".24" stop-color="#d3e6f1"/><stop offset=".49" stop-color="#738ea4"/><stop offset=".74" stop-color="#bedbea"/><stop offset="1" stop-color="#5f7d96"/></linearGradient><linearGradient id="atlas-wire-active-metal" gradientUnits="userSpaceOnUse" x2="480" spreadMethod="reflect"><stop stop-color="#487ca7"/><stop offset=".23" stop-color="#d1efff"/><stop offset=".48" stop-color="#609fcd"/><stop offset=".74" stop-color="#a7dbf2"/><stop offset="1" stop-color="#477fa9"/></linearGradient>';
  svg.append(metalDefs);
  svg.querySelectorAll('.edge').forEach(edge=>{const group=document.createElementNS(ns,'g'),shadow=document.createElementNS(ns,'path'),shine=document.createElementNS(ns,'path');group.classList.add('metal-link');shadow.classList.add('wire-shadow');shine.classList.add('wire-highlight');group.append(shadow,edge,shine);wires.append(group);links.push({edge,group,shadow,shine,index:byId.get(edge.dataset.to).deps.indexOf(edge.dataset.from),bounds:null,shown:null});});svg.append(wires);
  function displayHeight(p){return p.compact?p.h:detail==='full'?p.h:Math.min(p.h,(detail==='summary'?160:detail==='title'?82:36)*factor);}
  function portCenter(p,i=0){return p.compact?24*factor:detail==='full'?(174+22*i)*factor:displayHeight(p)/2;}
  function updateLinks(){
    const enabled=scopePicker.value!=='open';
    for(const {id,b} of entries){
      for(const port of b.querySelectorAll('.node-input-socket'))port.hidden=!enabled||!layout.has(port.dataset.premise)||isReferenceCard(byId.get(port.dataset.premise));
      const outputPort=b.querySelector('.node-output-socket');if(outputPort)outputPort.hidden=!enabled||!nodes.some(n=>layout.has(n.id)&&n.deps.includes(id));
    }
    for(const link of links){const {edge,group,shadow,shine}=link,a=layout.get(edge.dataset.from),b=layout.get(edge.dataset.to);link.bounds=null;
      group.classList.toggle('active',edge.classList.contains('active'));group.classList.toggle('assumed',edge.classList.contains('assumed'));
      if(!enabled||!a||!b)continue;
      const ax=a.x+306*factor,ay=a.y+portCenter(a),bx=b.x-6*factor,by=b.y+portCenter(b,link.index),bend=Math.max(75*factor,(bx-ax)*.5),d=`M ${ax} ${ay} C ${ax+bend} ${ay}, ${bx-bend} ${by}, ${bx} ${by}`;
      for(const path of [shadow,edge,shine])path.setAttribute('d',d);edge.removeAttribute('marker-end');
      link.bounds={left:Math.min(ax,bx,ax+bend,bx-bend),right:Math.max(ax,bx,ax+bend,bx-bend),top:Math.min(ay,by),bottom:Math.max(ay,by)};
    }
  }
  updateLinks();
  let zoom=1,x=0,y=0,drag=null,space=false,lastFrame='selected',initialized=false,viewSelection=selected(),motionFrame=0,motionTarget=null,lastCurrentGeometry='';
  const reducedMotion=matchMedia('(prefers-reduced-motion: reduce)');
  const controls=document.createElement('div');controls.className='editor-navigation';controls.innerHTML=`<button class="button small" data-frame="all" title="${t('显示全部 · Home')}">${t('显示全部')}</button><button class="button small" data-frame="selected" title="${t('聚焦所选 · 小数点键')}">${t('聚焦所选')}</button><button class="button small" data-node-zoom="in" aria-label="${t('放大')}">＋</button><button class="button small" data-node-zoom="out" aria-label="${t('缩小')}">−</button><output aria-label="${t('缩放比例')}">100%</output>`;viewport.append(controls);
  const output=controls.querySelector('output');viewport.tabIndex=0;viewport.setAttribute('role','region');viewport.setAttribute('aria-label',t('节点编辑区：拖动空白平移，滚轮缩放，Home 显示全部，小数点键聚焦。'));
  const theoremFocus=document.createElement('button');theoremFocus.type='button';theoremFocus.className='button small';theoremFocus.dataset.frame='theorem';theoremFocus.textContent=english?'Theorem':'最终定理';controls.insertBefore(theoremFocus,controls.firstChild);
  function paint(){if(!renderFrame)renderFrame=requestAnimationFrame(draw);}
  function draw(frameTime){
    renderFrame=0;if(document.hidden||!viewWidth||!viewHeight)return;
    const start=performance.now(),unit=zoom*factor,mode=unit<.28?'micro':unit<.52?'title':unit<.9?'summary':'full';
    if(mode!==detail){detail=mode;graph.dataset.detail=detail;revision++;updateLinks();}
    graph.style.setProperty('--node-unit',unit);
    const margin=90,clip={left:(-x-margin)/zoom,right:(viewWidth-x+margin)/zoom,top:(-y-margin)/zoom,bottom:(viewHeight-y+margin)/zoom};
    let visibleNodes=0,visibleLinks=0;
    for(const {p,b} of entries){const h=displayHeight(p),culled=p.x+300*factor<clip.left||p.x>clip.right||p.y+(p.compact?p.visibleH:h)<clip.top||p.y>clip.bottom;
      if(b._culled!==culled){b.classList.toggle('viewport-culled',culled);b._culled=culled;}
      if(culled)continue;visibleNodes++;
      b.style.setProperty('--node-x',Math.round(p.x*zoom+x)+'px');b.style.setProperty('--node-y',Math.round(p.y*zoom+y)+'px');
      if(b._unit!==unit||b._revision!==revision){b.style.width=300*unit+'px';b.style.height=h*zoom+'px';b.style.setProperty('--port-y',(portCenter(p)/factor-6)+'px');b._unit=unit;b._revision=revision;}
    }
    for(const link of links){const b=link.bounds,shown=!!b&&b.right>=clip.left&&b.left<=clip.right&&b.bottom>=clip.top&&b.top<=clip.bottom;
      if(shown)visibleLinks++;if(shown!==link.shown){link.group.style.display=shown?'':'none';link.shown=shown;}}
    theoremCard.place(theoremBox.x*zoom+x,theoremBox.y*zoom+y,unit);wires.setAttribute('transform',`translate(${x} ${y}) scale(${zoom})`);
    output.textContent=Math.round(zoom*100)+'%';viewport.style.backgroundSize=32*zoom+'px '+32*zoom+'px';viewport.style.backgroundPosition=x+'px '+y+'px';
    recordAtlasRender(start,{visibleNodes,totalNodes:nodes.length,visibleLinks,totalLinks:links.length},frameTime);
  }
  function placeSelection(){const p=layout.get(focusId());if(!p)return;const w=viewport.clientWidth,h=Math.max(1,viewport.clientHeight-50),cardW=300*factor*zoom,cardH=(p.visibleH||p.h)*zoom,hasPremises=byId.get(focusId()).deps.length>0;const left=Math.max(24,Math.min(w-cardW-24,w*(hasPremises?.76:.45)-cardW/2));return {x:left-p.x*zoom,y:Math.max(20,(h-cardH)/2)-p.y*zoom};}
  function stopMotion(finish=false){
    if(motionFrame)cancelAnimationFrame(motionFrame);motionFrame=0;
    if(finish&&motionTarget){x=motionTarget.x;y=motionTarget.y;paint();}
    motionTarget=null;viewport.dataset.cameraMoving='false';
  }
  function moveSelection(){const target=placeSelection();if(!target)return;
    stopMotion();
    const dx=target.x-x,dy=target.y-y,distance=Math.hypot(dx,dy);
    if(distance<.5||reducedMotion.matches||document.documentElement.dataset.panAnimation==='false'){
      x=target.x;y=target.y;paint();return;
    }
    const fromX=x,fromY=y,duration=Math.min(600,Math.max(360,320+Math.sqrt(distance)*6)),start=performance.now();
    motionTarget=target;viewport.dataset.cameraMoving='true';paint();
    function tick(now){const u=Math.min(1,(now-start)/duration),ease=u*u*u*(u*(u*6-15)+10);
      x=fromX+dx*ease;y=fromY+dy*ease;paint();
      if(u<1)motionFrame=requestAnimationFrame(tick);
      else {motionFrame=0;motionTarget=null;viewport.dataset.cameraMoving='false';}
    }
    motionFrame=requestAnimationFrame(tick);
  }
  window.addEventListener('motionchange',()=>{if(document.documentElement.dataset.panAnimation==='false')stopMotion(true);});
  reducedMotion.addEventListener('change',()=>{if(reducedMotion.matches)stopMotion(true);});
  function frame(mode=lastFrame){stopMotion();lastFrame=mode;const id=focusId(),ids=mode==='theorem'?[]:mode==='all'?[...layout.keys()]:(layout.get(id)?.base?[id]:[id,...byId.get(id).deps]).filter(id=>layout.has(id));theoremBox=theoremCard.layout(layout,factor);const pts=[...ids.map(id=>({...layout.get(id),h:layout.get(id).visibleH||layout.get(id).h,w:300*factor})),...(mode==='selected'?[]:[theoremBox])],loX=Math.min(...pts.map(p=>p.x))-45,loY=Math.min(...pts.map(p=>p.y))-45,hiX=Math.max(...pts.map(p=>p.x+p.w))+45,hiY=Math.max(...pts.map(p=>p.y+p.h))+45;const w=viewport.clientWidth,h=viewport.clientHeight-50;if(!w||!h)return;zoom=Math.min(w/(hiX-loX),h/(hiY-loY),mode==='theorem'?1.4:1.1);x=(w-(hiX-loX)*zoom)/2-loX*zoom;y=(h-(hiY-loY)*zoom)/2-loY*zoom;paint();}
  function scale(f,cx=viewport.clientWidth/2,cy=viewport.clientHeight/2){stopMotion();const next=Math.max(.18,Math.min(2.2,zoom*f));x=cx-(cx-x)*next/zoom;y=cy-(cy-y)*next/zoom;zoom=next;paint();}
  viewport.addEventListener('wheel',e=>{e.preventDefault();const box=viewport.getBoundingClientRect();scale(Math.exp(-e.deltaY*.0015),e.clientX-box.left,e.clientY-box.top);},{passive:false});
  viewport.addEventListener('pointerdown',e=>{if(e.target.closest('.editor-navigation,.source-packs,.theorem-target-actions,.theorem-target-conventions'))return;if(e.button!==1&&e.button!==0)return;if(e.target.closest('.node,.theorem-target-card')&&!space&&e.button!==1)return;stopMotion();drag={id:e.pointerId,x:e.clientX,y:e.clientY};viewport.setPointerCapture(e.pointerId);viewport.classList.add('panning');e.preventDefault();});
  viewport.addEventListener('pointermove',e=>{if(!drag||e.pointerId!==drag.id)return;x+=e.clientX-drag.x;y+=e.clientY-drag.y;drag.x=e.clientX;drag.y=e.clientY;paint();});
  const end=()=>{drag=null;viewport.classList.remove('panning');};viewport.addEventListener('pointerup',end);viewport.addEventListener('pointercancel',end);
  viewport.addEventListener('keydown',e=>{if(e.target.closest('input,select'))return;if(e.code==='Space'){space=true;e.preventDefault();}else if(e.key==='Home'){e.preventDefault();frame('all');}else if(e.key==='.'||e.code==='NumpadDecimal'){e.preventDefault();frame('selected');}else if(['+','=','-'].includes(e.key)){e.preventDefault();scale(e.key==='-'?.85:1.15);}else if(e.key.startsWith('Arrow')){e.preventDefault();stopMotion();if(e.key==='ArrowLeft')x+=45;if(e.key==='ArrowRight')x-=45;if(e.key==='ArrowUp')y+=45;if(e.key==='ArrowDown')y-=45;paint();}});viewport.addEventListener('keyup',()=>space=false);viewport.addEventListener('blur',()=>space=false);
  controls.querySelectorAll('[data-frame]').forEach(b=>b.onclick=()=>frame(b.dataset.frame));controls.querySelectorAll('[data-node-zoom]').forEach(b=>b.onclick=()=>scale(b.dataset.nodeZoom==='in'?1.15:1/1.15));new ResizeObserver(es=>{viewWidth=es[0].contentRect.width;viewHeight=es[0].contentRect.height;graph.style.width=viewWidth+'px';graph.style.minHeight=viewHeight+'px';svg.style.width=viewWidth+'px';svg.style.height=viewHeight+'px';if(!viewWidth||!viewHeight)return;if(!initialized){initialized=true;frame();}else paint();}).observe(viewport);
  window.addEventListener('typographychange',()=>{stopMotion();const prior=layout.get(focusId()),cx=(prior.x+150*factor)*zoom+x,cy=(prior.y+prior.h/2)*zoom+y;buildLayout();updateLinks();const next=layout.get(focusId());x=cx-(next.x+150*factor)*zoom;y=cy-(next.y+next.h/2)*zoom;paint();});
  theoremCard.element.addEventListener('theoremcardchange',()=>{stopMotion();buildLayout();updateLinks();paint();});
  function selectionChanged(){
    sourcePacks.selectionChanged();referenceNotice.hidden=!isReferenceCard(byId.get(selected()));referenceNotice.textContent=english?'Reference card opened in its pack · proof view retained':'已在卡包中打开引用卡片 · 主证明视图保留';if(isReferenceCard(byId.get(selected()))&&!worldContext?.reference){paint();return;}diagramSelection=selected();stopMotion();const id=selected(),prior=layout.get(id),anchor=prior?{x:prior.x*zoom+x,y:prior.y*zoom+y}:null;
    const changed=id!==viewSelection;viewSelection=id;buildLayout();updateLinks();
    if(!initialized){initialized=true;requestAnimationFrame(()=>frame());return;}
    const next=layout.get(id);
    if(next&&anchor){x=anchor.x-next.x*zoom;y=anchor.y-next.y*zoom;}
    if(changed)moveSelection();else paint();
  }
  function refreshLanguage(){sourcePacks.refreshLanguage();nodes.forEach(n=>{const b=cards.get(n.id);b.querySelector('.node-heading').textContent=n.title;b.querySelector('.node-heading').title=n.title;b.querySelector('.node-proposition').innerHTML=graphStatement(n,english);n.deps.forEach((id,i)=>{const row=b.querySelectorAll('.node-input')[i];const d=byId.get(id);if(isReferenceCard(d))row.innerHTML=`<span class="reference-pack-tag">${escapeHTML(packLabel(d,english))}</span>${escapeHTML(d.title)}`;else row.textContent=d.title;row.title=d.title;});b.querySelector('.node-summary').textContent=n.deps.length?(english?n.deps.length+(n.deps.length===1?' premise':' premises'):n.deps.length+' 个前提'):(english?'Source card':'来源卡片');b.querySelector('.node-output').textContent=t('结论');b.querySelector('small').textContent=t(({done:'✓ Lean 已验证',conditional:'✓ Lean 已验证 · 辅助定理',assumption:'? 暂作假设',pending:'○ 待完成目标'})[n.status]);});paint();}
  graph.dataset.detail=detail;
  document.addEventListener('visibilitychange',()=>{if(document.hidden)stopMotion();else paint();});
  return {getCamera(){return {zoom,x,y,lastFrame};},restoreCamera(camera){if(camera){stopMotion();({zoom,x,y,lastFrame}=camera);paint();}},setWorldContext(context){worldContext=context;theoremCard.setTarget(context.target);buildLayout();updateLinks();paint();},show(){requestAnimationFrame(()=>{if(!initialized){initialized=true;frame();}else paint();});},selectionChanged,frame,refreshLanguage};
}
