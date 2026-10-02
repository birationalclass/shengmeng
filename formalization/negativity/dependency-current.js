// Decorative dependency traversal; it never changes proof status or semantic edges.
export function installDependencyCurrent({nodes,graph,svg,selected,spatialHost,english}) {
  const ns='http://www.w3.org/2000/svg',byId=new Map(nodes.map(n=>[n.id,n]));
  const stylesheet=document.createElement('link');stylesheet.rel='stylesheet';
  stylesheet.href=new URL('./dependency-current.css?v=20261002-current-1',import.meta.url).href;
  document.head.append(stylesheet);
  const note=document.createElement('span');note.className='dependency-current-note';
  note.textContent=english?'Flow: premise → result':'流光：前提 → 结论';
  note.title=english?'Dependency traversal only. Proof status comes from the badges; open inputs stop the flow.':'流光展示依赖方向。验证状态看徽章；未完成输入会阻断流光。';
  document.querySelector('.relation-legend').append(note);
  const spatialStage=spatialHost.querySelector('.spatial-stage');
  const spatialOverlay=document.createElementNS(ns,'svg');
  spatialOverlay.classList.add('dependency-current-spatial');spatialOverlay.setAttribute('aria-hidden','true');
  spatialStage.insertBefore(spatialOverlay,spatialStage.querySelector('.spatial-cards'));
  const reduced=matchMedia('(prefers-reduced-motion: reduce)');
  const pulses=new Map(),halos=new Map();let frame=0,epoch=0,lastSelection='';
  const proven=id=>['done','conditional'].includes(byId.get(id)?.status);
  function chain(id,result=new Set()) {if(result.has(id))return result;result.add(id);byId.get(id).deps.forEach(p=>chain(p,result));return result;}
  function schedule(){if(!frame)frame=requestAnimationFrame(refresh);}
  function cancel(record){record.animations.forEach(a=>a.cancel());record.animations=[];}
  function remove(map,key){const record=map.get(key);cancel(record);record.elements.forEach(e=>e.remove());map.delete(key);}
  function keyframes(start,end,period,from,to){
    // All incoming branches finish at the same node stage; the next hop starts there.
    const a=Math.max(.001,start/period),b=Math.min(.985,end/period);
    return [{offset:0,opacity:0,strokeDashoffset:from},
      {offset:a,opacity:0,strokeDashoffset:from},
      {offset:Math.min(a+.012,b),opacity:1,strokeDashoffset:from},
      {offset:b,opacity:1,strokeDashoffset:to},
      {offset:Math.min(b+.012,1),opacity:0,strokeDashoffset:to},
      {offset:1,opacity:0,strokeDashoffset:to}];
  }
  function animatePulse(record,signature,start,end,period){
    if(record.signature===signature)return;
    cancel(record);record.signature=signature;
    record.elements.forEach(e=>e.classList.toggle('dependency-current-static',reduced.matches));
    if(reduced.matches)return;
    record.animations=record.elements.map(e=>e.animate(keyframes(start,end,period,'16','-100'),
      {duration:period,iterations:Infinity,easing:'linear'}));
    record.animations.forEach(a=>a.startTime=epoch);
  }
  function syncHalo(key,card,signature,arrival,period){
    let record=halos.get(key);
    if(!record){const e=document.createElement('span');e.className='dependency-current-halo';
      e.setAttribute('aria-hidden','true');card.append(e);record={elements:[e],animations:[],signature:''};halos.set(key,record);}
    if(record.signature===signature)return;
    cancel(record);record.signature=signature;
    if(reduced.matches)return;
    const a=Math.min(.89,Math.max(.01,arrival/period)),b=Math.min(.99,a+380/period);
    record.animations=[record.elements[0].animate([{offset:0,opacity:0},{offset:a,opacity:0},
      {offset:Math.min(a+.015,b),opacity:1},{offset:b,opacity:0},{offset:1,opacity:0}],
      {duration:period,iterations:Infinity,easing:'ease-out'})];
    record.animations.forEach(a=>a.startTime=epoch);
  }
  function makePulse(key,parent){
    let record=pulses.get(key);if(record)return record;
    const elements=['glow','core'].map(layer=>{const p=document.createElementNS(ns,'path');
      p.classList.add('dependency-current-'+layer);p.setAttribute('pathLength','100');
      p.setAttribute('aria-hidden','true');parent.append(p);return p;});
    record={elements,animations:[],signature:''};pulses.set(key,record);return record;
  }
  function refresh(){frame=0;const id=selected(),ancestors=chain(id),ready=new Map();
    if(lastSelection!==id){epoch=document.timeline.currentTime;lastSelection=id;}
    function complete(key){if(ready.has(key))return ready.get(key);
      const ok=proven(key)&&byId.get(key).deps.every(complete);ready.set(key,ok);return ok;}
    ancestors.forEach(complete);
    const keepPulses=new Set(),keepHalos=new Set();
    for(const view of ['2d','3d']){
      const cards=new Map(nodes.map(n=>[n.id,view==='2d'?graph.querySelector(`[data-node="${n.id}"]`):spatialHost.querySelector(`[data-spatial-node="${n.id}"]`)]));
      const visible=key=>ancestors.has(key)&&cards.get(key)&&!cards.get(key).hidden;
      const ranks=new Map();function rank(key){if(!ranks.has(key))ranks.set(key,Math.max(-1,...byId.get(key).deps.filter(visible).map(rank))+1);return ranks.get(key);}
      const routes=[...svg.querySelectorAll('.edge')].filter(edge=>visible(edge.dataset.from)&&visible(edge.dataset.to)&&
        ready.get(edge.dataset.from)&&ready.get(edge.dataset.to)&&edge.classList.contains('active')&&
        (view==='3d'?document.querySelector('#scope').value!=='open':edge.style.display!=='none'&&edge.parentElement.style.display!=='none')&&
        !(view==='3d'&&spatialHost.querySelector('[data-camera="direct"]').getAttribute('aria-pressed')==='true'&&edge.dataset.to!==id));
      const hop=620,maximum=Math.max(1,...routes.map(e=>rank(e.dataset.to))),period=Math.max(3000,maximum*hop+1500);
      const stageBox=spatialStage.getBoundingClientRect();
      if(view==='3d'){spatialOverlay.setAttribute('viewBox',`0 0 ${Math.max(1,stageBox.width)} ${Math.max(1,stageBox.height)}`);}
      const involved=new Set();
      routes.forEach(edge=>{
        const from=edge.dataset.from,to=edge.dataset.to,key=view+':'+from+':'+to;
        involved.add(from);involved.add(to);keepPulses.add(key);
        const record=makePulse(key,view==='2d'?edge.parentElement:spatialOverlay);
        let d=edge.getAttribute('d');
        if(view==='3d'){
          const a=cards.get(from).getBoundingClientRect(),b=cards.get(to).getBoundingClientRect();
          d=`M ${a.x+a.width/2-stageBox.x} ${a.y+a.height/2-stageBox.y} L ${b.x+b.width/2-stageBox.x} ${b.y+b.height/2-stageBox.y}`;
        }
        record.elements.forEach(p=>{if(p.getAttribute('d')!==d)p.setAttribute('d',d);});
        const end=rank(to)*hop,start=Math.max(0,end-hop);
        animatePulse(record,[id,reduced.matches,start,end,period].join(':'),start,end,period);
      });
      involved.forEach(key=>{
        const card=cards.get(key),arrival=rank(key)*hop,haloKey=view+':'+key;
        keepHalos.add(haloKey);syncHalo(haloKey,card,[id,reduced.matches,arrival,period].join(':'),arrival,period);
      });
    }
    [...pulses.keys()].filter(k=>!keepPulses.has(k)).forEach(k=>remove(pulses,k));
    [...halos.keys()].filter(k=>!keepHalos.has(k)).forEach(k=>remove(halos,k));
    pauseHiddenViews();
  }
  function pauseHiddenViews(){for(const [key,record] of [...pulses,...halos]){
    const hidden=document.hidden||(key.startsWith('2d:')?graph.closest('.graph-scroll').hidden:spatialHost.hidden);
    record.animations.forEach(a=>{if(hidden&&a.playState==='running')a.pause();else if(!hidden&&a.playState==='paused')a.play();});
  }}
  // Observe viewer geometry and selection only; ignore our own decorative mutations.
  const observer=new MutationObserver(records=>{
    if(records.some(r=>r.target.matches?.('.edge,.node,.spatial-node,#spatialGraph,.graph-scroll,[data-camera="direct"]')))schedule();
  });
  observer.observe(graph,{subtree:true,attributes:true,attributeFilter:['d','class','aria-pressed','hidden']});
  observer.observe(spatialHost,{subtree:true,attributes:true,attributeFilter:['style','hidden','data-relation','aria-pressed']});
  observer.observe(graph.closest('.graph-scroll'),{attributes:true,attributeFilter:['hidden']});
  new ResizeObserver(schedule).observe(spatialStage);
  document.addEventListener('visibilitychange',pauseHiddenViews);
  reduced.addEventListener('change',schedule);
  schedule();
}
