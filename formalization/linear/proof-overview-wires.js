import {visibleOverviewEdges} from './proof-overview-model.js?v=20261011-linear-83';

export function drawOverviewWires({scene,wires,deck,target,model,scale,english,escapeHTML}){
  const screen=scene.getBoundingClientRect(),cards=new Map();
  for(const card of deck.querySelectorAll('.node[data-world-node]'))cards.set(card.dataset.worldNode,card);
  const edges=visibleOverviewEdges(model,[...cards.keys()]);cards.set('lemma',target);
  for(const card of cards.values()){
    card.querySelectorAll('.world-connection-port').forEach(port=>port.remove());
    card.querySelectorAll('.node-input-socket,.node-output-socket,.world-source-port,.theorem-port').forEach(port=>port.hidden=true);
  }
  const rect=card=>{const r=card.getBoundingClientRect();return {x:(r.left-screen.left)/scale,y:(r.top-screen.top)/scale,w:r.width/scale,h:r.height/scale};};
  const port=(card,side)=>{
    if(card.querySelector(`.world-connection-port[data-side="${side}"]`))return;
    const el=document.createElement('span');el.className='world-connection-port';el.dataset.side=side;el.setAttribute('aria-hidden','true');card.append(el);
  };
  const endpoint=(r,side)=>side==='left'?{x:r.x-6,y:r.y+r.h/2}:side==='right'?{x:r.x+r.w+6,y:r.y+r.h/2}:side==='top'?{x:r.x+r.w/2,y:r.y-6}:{x:r.x+r.w/2,y:r.y+r.h+6};
  const control=(p,side,bend)=>({x:p.x+(side==='left'?-bend:side==='right'?bend:0),y:p.y+(side==='top'?-bend:side==='bottom'?bend:0)});
  let html='<defs><linearGradient id="world-wire-metal" x2="100%"><stop stop-color="#66859e"/><stop offset=".45" stop-color="#cee8f6"/><stop offset="1" stop-color="#638eae"/></linearGradient></defs>';
  for(const edge of edges){
    const source=cards.get(edge.source),destination=cards.get(edge.target),aRect=rect(source),bRect=rect(destination);
    const dx=bRect.x+bRect.w/2-aRect.x-aRect.w/2,dy=bRect.y+bRect.h/2-aRect.y-aRect.h/2;
    const horizontal=Math.abs(dx)>Math.abs(dy),from=horizontal?(dx>0?'right':'left'):(dy>0?'bottom':'top'),to=horizontal?(dx>0?'left':'right'):(dy>0?'top':'bottom');
    const a=endpoint(aRect,from),b=endpoint(bRect,to),bend=Math.max(16,(horizontal?Math.abs(a.x-b.x):Math.abs(a.y-b.y))*.38),ca=control(a,from,bend),cb=control(b,to,bend);
    port(source,from);port(destination,to);
    const label=english?'Manuscript proof reading route; not a compiler dependency':'原稿证明阅读路径；不是编译器依赖';
    const d=`M${a.x} ${a.y} C${ca.x} ${ca.y},${cb.x} ${cb.y},${b.x} ${b.y}`;
    html+=`<g class="world-wire" data-source="${escapeHTML(edge.source)}" data-target="${escapeHTML(edge.target)}" data-relation="reading" data-route-kind="${edge.kind}"><title>${escapeHTML(label)}</title><path class="world-wire-shadow" d="${d}"/><path class="world-wire-body" d="${d}"/><path class="world-wire-shine" d="${d}"/></g>`;
  }
  wires.setAttribute('viewBox',`0 0 ${scene.clientWidth} ${scene.clientHeight}`);wires.innerHTML=html;
}
