import {visibleProofIds,compactProofLayout} from './proof-layout.js?v=20261002-formal-18';
import {t,english} from './i18n.js?v=20261002-refuge-1&proof=20261002-formal-23';
// Viewer-only node editor: sockets and links always use the curated proof DAG.
export function createNodeEditor({viewport,graph,svg,nodes,select,selected,theoremTarget}) {
  const byId=new Map(nodes.map(n=>[n.id,n]));let layout=new Map(),factor=1,expandedInputs=false;
  const theoremCard=theoremTarget.createCard('2d');graph.append(theoremCard.element);let theoremBox;
  function buildLayout(){factor=parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--node-base-font'))/16||1.125;const scope=document.querySelector('#scope').value;const ids=visibleProofIds(nodes,selected(),scope);layout=compactProofLayout(nodes,ids,factor,scope==='direct'?3:5,{selected:selected(),expandedInputs});graph.querySelectorAll('.node').forEach(b=>b.hidden=!ids.has(b.dataset.node));theoremBox=theoremCard.layout(layout,factor);}
  buildLayout();
  graph.querySelectorAll('.column-label').forEach(e=>e.remove());
  nodes.forEach(n=>{const p=layout.get(n.id)||{x:0,y:0,h:150*factor},b=graph.querySelector(`[data-node="${n.id}"]`);b.style.left=p.x+'px';b.style.top=p.y+'px';b.style.height=p.h+'px';b.style.setProperty('--node-x',p.x+'px');b.style.setProperty('--node-y',p.y+'px');b.innerHTML='';const heading=document.createElement('b');heading.className='node-heading';heading.textContent=n.title;heading.title=n.title;b.append(heading);const sockets=document.createElement('div');sockets.className='node-sockets';
    if(!n.deps.length){const row=document.createElement('span');row.className='node-input empty-input';row.textContent='';sockets.append(row);}n.deps.forEach(id=>{const row=document.createElement('span');row.className='node-input';row.textContent=byId.get(id).title;row.title=byId.get(id).title;sockets.append(row);});b.append(sockets);const output=document.createElement('span');output.className='node-output';output.textContent=t('结论');b.append(output);const status=document.createElement('small');status.className=n.status;status.textContent=t(({done:'✓ Lean 已验证',conditional:'◐ 条件式证明 · 输入未齐',assumption:'? 暂作假设',pending:'○ 待完成目标'})[n.status]);b.append(status);const rel=document.createElement('span');rel.className='relation-tag';b.append(rel);});
  // Half-round ports sit outside the card; wires meet the outer arc, not the text.
  nodes.forEach(n=>{const b=graph.querySelector(`[data-node="${n.id}"]`);n.deps.forEach((_,i)=>{const inputPort=document.createElement('span');inputPort.className='node-input-socket';inputPort.setAttribute('aria-hidden','true');inputPort.style.setProperty('--socket-y',(58+22*i)+'px');b.append(inputPort);});const outputPort=document.createElement('span');outputPort.className='node-output-socket';outputPort.setAttribute('aria-hidden','true');b.append(outputPort);});
  const inputRail=document.createElement('div');inputRail.className='base-input-rail';
  const railLabel=document.createElement('span'),railToggle=document.createElement('button');
  railToggle.type='button';railToggle.className='input-rail-toggle';
  const railHeader=document.createElement('div');railHeader.className='base-input-controls';
  Object.assign(railHeader.style,{position:'absolute',zIndex:'100',display:'flex',justifyContent:'space-between',alignItems:'center',gap:'8px',boxSizing:'border-box',padding:'6px 8px',borderRadius:'10px',background:'#edf4fad9',color:'#566f7b'});
  railHeader.append(railLabel,railToggle);inputRail.append(railHeader);graph.append(inputRail);
  railToggle.onclick=()=>{stopMotion();const id=selected(),prior=layout.get(id),anchor=prior?{x:prior.x*zoom+x,y:prior.y*zoom+y}:null;expandedInputs=!expandedInputs;buildLayout();updateLinks();const next=layout.get(id);if(anchor&&next){x=anchor.x-next.x*zoom;y=anchor.y-next.y*zoom;}paint();};
  const ns='http://www.w3.org/2000/svg',wires=document.createElementNS(ns,'g'),links=[];
  const metalDefs=document.createElementNS(ns,'defs');
  metalDefs.innerHTML='<linearGradient id="atlas-wire-metal" gradientUnits="userSpaceOnUse" x2="480" spreadMethod="reflect"><stop stop-color="#6b879d"/><stop offset=".24" stop-color="#d3e6f1"/><stop offset=".49" stop-color="#738ea4"/><stop offset=".74" stop-color="#bedbea"/><stop offset="1" stop-color="#5f7d96"/></linearGradient><linearGradient id="atlas-wire-active-metal" gradientUnits="userSpaceOnUse" x2="480" spreadMethod="reflect"><stop stop-color="#487ca7"/><stop offset=".23" stop-color="#d1efff"/><stop offset=".48" stop-color="#609fcd"/><stop offset=".74" stop-color="#a7dbf2"/><stop offset="1" stop-color="#477fa9"/></linearGradient>';
  svg.append(metalDefs);
  svg.querySelectorAll('.edge').forEach(edge=>{const group=document.createElementNS(ns,'g'),shadow=document.createElementNS(ns,'path'),shine=document.createElementNS(ns,'path');group.classList.add('metal-link');shadow.classList.add('wire-shadow');shine.classList.add('wire-highlight');group.append(shadow,edge,shine);wires.append(group);links.push({edge,group,shadow,shine});});svg.append(wires);
  function updateLinks(){links.forEach(({edge,group,shadow,shine})=>{const a=layout.get(edge.dataset.from),n=byId.get(edge.dataset.to),b=layout.get(n.id);const shown=Boolean(a&&b)&&document.querySelector('#scope').value!=='open';group.style.display=shown?'':'none';group.classList.toggle('active',edge.classList.contains('active'));group.classList.toggle('assumed',edge.classList.contains('assumed'));if(!shown)return;const x=a.x+306*factor,y=a.y+(a.compact?24:64)*factor,x2=b.x-6*factor,y2=b.y+(64+22*n.deps.indexOf(edge.dataset.from))*factor,bend=Math.max(75*factor,(x2-x)*.5),d=`M ${x} ${y} C ${x+bend} ${y}, ${x2-bend} ${y2}, ${x2} ${y2}`;[shadow,edge,shine].forEach(p=>p.setAttribute('d',d));edge.removeAttribute('marker-end');});}
  updateLinks();
  let zoom=1,x=0,y=0,drag=null,space=false,lastFrame='selected',initialized=false,viewSelection=selected(),motionFrame=0,motionTarget=null,lastCurrentGeometry='';
  const reducedMotion=matchMedia('(prefers-reduced-motion: reduce)');
  const controls=document.createElement('div');controls.className='editor-navigation';controls.innerHTML=`<button class="button small" data-frame="all" title="${t('显示全部 · Home')}">${t('显示全部')}</button><button class="button small" data-frame="selected" title="${t('聚焦所选 · 小数点键')}">${t('聚焦所选')}</button><button class="button small" data-node-zoom="in" aria-label="${t('放大')}">＋</button><button class="button small" data-node-zoom="out" aria-label="${t('缩小')}">−</button><output aria-label="${t('缩放比例')}">100%</output>`;viewport.append(controls);
  const output=controls.querySelector('output');viewport.tabIndex=0;viewport.setAttribute('role','region');viewport.setAttribute('aria-label',t('节点编辑区：拖动空白平移，滚轮缩放，Home 显示全部，小数点键聚焦。'));
  const theoremFocus=document.createElement('button');theoremFocus.type='button';theoremFocus.className='button small';theoremFocus.dataset.frame='theorem';theoremFocus.textContent=english?'Theorem':'最终定理';controls.insertBefore(theoremFocus,controls.firstChild);
  function paint(){graph.classList.toggle('zoom-compact',zoom<.52);graph.style.transform='none';graph.style.width=viewport.clientWidth+'px';graph.style.minHeight=viewport.clientHeight+'px';graph.style.setProperty('--node-unit',zoom*factor);graph.style.setProperty('--view-x',x+'px');graph.style.setProperty('--view-y',y+'px');nodes.forEach(n=>{const p=layout.get(n.id);if(!p)return;const b=graph.querySelector(`[data-node="${n.id}"]`);b.classList.toggle('base-card',Boolean(p.base));b.classList.toggle('compact-input',Boolean(p.compact));b.dataset.baseInput=String(Boolean(p.base));b.style.zIndex=String(p.base?10+p.stackIndex:2);b.style.setProperty('--node-x',p.x*zoom+x+'px');b.style.setProperty('--node-y',p.y*zoom+y+'px');b.style.width=(300*factor*zoom)+'px';b.style.height=(p.h*zoom)+'px';});const roots=[...layout.values()].filter(p=>p.base);inputRail.hidden=!roots.length;
    railHeader.style.display=roots.length?'flex':'none';
    if(roots.length){const top=Math.min(...roots.map(p=>p.y)),bottom=Math.max(...roots.map(p=>p.y+p.h));
      inputRail.style.left=((65-18*factor)*zoom+x)+'px';inputRail.style.top=((top-42*factor)*zoom+y)+'px';
      inputRail.style.width=336*factor*zoom+'px';inputRail.style.height=(bottom-top+60*factor)*zoom+'px';
      inputRail.style.fontSize=12*factor*zoom+'px';inputRail.style.padding=10*factor*zoom+'px';
      // The controls belong to the group frame and share its camera geometry.
      const unit=factor*zoom;
      railHeader.style.left=10*unit+'px';railHeader.style.top=10*unit+'px';
      railHeader.style.width=316*unit+'px';railHeader.style.fontSize=12*unit+'px';
      railHeader.style.padding=6*unit+'px '+8*unit+'px';
      railHeader.style.gap=8*unit+'px';railHeader.style.borderRadius=10*unit+'px';
      inputRail.style.borderRadius=18*unit+'px';
      railLabel.textContent=t('基础输入')+' · '+roots.length;
      railToggle.hidden=roots.length<=1;railToggle.textContent=t(expandedInputs?'折叠纸牌':'展开纸牌');railToggle.setAttribute('aria-expanded',String(expandedInputs));
    }
    theoremCard.place(theoremBox.x*zoom+x,theoremBox.y*zoom+y,zoom*factor);
    svg.style.width=viewport.clientWidth+'px';svg.style.height=viewport.clientHeight+'px';wires.setAttribute('transform',`translate(${x} ${y}) scale(${zoom})`);output.textContent=Math.round(zoom*100)+'%';viewport.style.backgroundSize=(32*zoom)+'px '+(32*zoom)+'px';viewport.style.backgroundPosition=x+'px '+y+'px';const geometry=zoom+':'+factor;if(geometry!==lastCurrentGeometry){lastCurrentGeometry=geometry;window.dispatchEvent(new Event('atlasgeometrychange'));}}
  function placeSelection(){const p=layout.get(selected());if(!p)return;const w=viewport.clientWidth,h=Math.max(1,viewport.clientHeight-50),cardW=300*factor*zoom,cardH=(p.visibleH||p.h)*zoom,hasPremises=byId.get(selected()).deps.length>0;const left=Math.max(24,Math.min(w-cardW-24,w*(hasPremises?.76:.45)-cardW/2));return {x:left-p.x*zoom,y:Math.max(20,(h-cardH)/2)-p.y*zoom};}
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
  function frame(mode=lastFrame){stopMotion();lastFrame=mode;const id=selected(),ids=mode==='theorem'?[]:mode==='all'?[...layout.keys()]:(layout.get(id)?.base?[id]:[id,...byId.get(id).deps]).filter(id=>layout.has(id));theoremBox=theoremCard.layout(layout,factor);const pts=[...ids.map(id=>({...layout.get(id),h:layout.get(id).visibleH||layout.get(id).h,w:300*factor})),...(mode==='selected'?[]:[theoremBox])],loX=Math.min(...pts.map(p=>p.x))-45,loY=Math.min(...pts.map(p=>p.y))-45,hiX=Math.max(...pts.map(p=>p.x+p.w))+45,hiY=Math.max(...pts.map(p=>p.y+p.h))+45;const w=viewport.clientWidth,h=viewport.clientHeight-50;if(!w||!h)return;zoom=Math.min(w/(hiX-loX),h/(hiY-loY),mode==='theorem'?1.4:1.1);x=(w-(hiX-loX)*zoom)/2-loX*zoom;y=(h-(hiY-loY)*zoom)/2-loY*zoom;paint();}
  function scale(f,cx=viewport.clientWidth/2,cy=viewport.clientHeight/2){stopMotion();const next=Math.max(.18,Math.min(2.2,zoom*f));x=cx-(cx-x)*next/zoom;y=cy-(cy-y)*next/zoom;zoom=next;paint();}
  viewport.addEventListener('wheel',e=>{e.preventDefault();const box=viewport.getBoundingClientRect();scale(Math.exp(-e.deltaY*.0015),e.clientX-box.left,e.clientY-box.top);},{passive:false});
  viewport.addEventListener('pointerdown',e=>{if(e.target.closest('.editor-navigation,.base-input-controls,.theorem-target-actions,.theorem-target-conventions'))return;if(e.button!==1&&e.button!==0)return;if(e.target.closest('.node,.theorem-target-card')&&!space&&e.button!==1)return;stopMotion();drag={id:e.pointerId,x:e.clientX,y:e.clientY};viewport.setPointerCapture(e.pointerId);viewport.classList.add('panning');e.preventDefault();});
  viewport.addEventListener('pointermove',e=>{if(!drag||e.pointerId!==drag.id)return;x+=e.clientX-drag.x;y+=e.clientY-drag.y;drag.x=e.clientX;drag.y=e.clientY;paint();});
  const end=()=>{drag=null;viewport.classList.remove('panning');};viewport.addEventListener('pointerup',end);viewport.addEventListener('pointercancel',end);
  viewport.addEventListener('keydown',e=>{if(e.target.closest('input,select'))return;if(e.code==='Space'){space=true;e.preventDefault();}else if(e.key==='Home'){e.preventDefault();frame('all');}else if(e.key==='.'||e.code==='NumpadDecimal'){e.preventDefault();frame('selected');}else if(['+','=','-'].includes(e.key)){e.preventDefault();scale(e.key==='-'?.85:1.15);}else if(e.key.startsWith('Arrow')){e.preventDefault();stopMotion();if(e.key==='ArrowLeft')x+=45;if(e.key==='ArrowRight')x-=45;if(e.key==='ArrowUp')y+=45;if(e.key==='ArrowDown')y-=45;paint();}});viewport.addEventListener('keyup',()=>space=false);viewport.addEventListener('blur',()=>space=false);
  controls.querySelectorAll('[data-frame]').forEach(b=>b.onclick=()=>frame(b.dataset.frame));controls.querySelectorAll('[data-node-zoom]').forEach(b=>b.onclick=()=>scale(b.dataset.nodeZoom==='in'?1.15:1/1.15));new ResizeObserver(()=>{if(!viewport.clientWidth||!viewport.clientHeight)return;if(!initialized){initialized=true;frame();}else paint();}).observe(viewport);
  window.addEventListener('typographychange',()=>{stopMotion();const prior=layout.get(selected()),cx=(prior.x+150*factor)*zoom+x,cy=(prior.y+prior.h/2)*zoom+y;buildLayout();updateLinks();const next=layout.get(selected());x=cx-(next.x+150*factor)*zoom;y=cy-(next.y+next.h/2)*zoom;paint();});
  theoremCard.element.addEventListener('theoremcardchange',()=>{stopMotion();buildLayout();updateLinks();paint();});
  function selectionChanged(){
    stopMotion();const id=selected(),prior=layout.get(id),anchor=prior?{x:prior.x*zoom+x,y:prior.y*zoom+y}:null;
    const changed=id!==viewSelection;viewSelection=id;buildLayout();updateLinks();
    if(!initialized){initialized=true;requestAnimationFrame(()=>frame());return;}
    const next=layout.get(id);
    if(next&&anchor){x=anchor.x-next.x*zoom;y=anchor.y-next.y*zoom;}
    if(changed)moveSelection();else paint();
  }
  function refreshLanguage(){nodes.forEach(n=>{const b=graph.querySelector(`[data-node="${n.id}"]`);b.querySelector('.node-heading').textContent=n.title;b.querySelector('.node-heading').title=n.title;n.deps.forEach((id,i)=>{const row=b.querySelectorAll('.node-input')[i];row.textContent=byId.get(id).title;row.title=byId.get(id).title;});b.querySelector('.node-output').textContent=t('结论');b.querySelector('small').textContent=t(({done:'✓ Lean 已验证',conditional:'◐ 条件式证明 · 输入未齐',assumption:'? 暂作假设',pending:'○ 待完成目标'})[n.status]);});paint();}
  return {show(){requestAnimationFrame(()=>{if(!initialized){initialized=true;frame();}else paint();});},selectionChanged,frame,refreshLanguage};
}
