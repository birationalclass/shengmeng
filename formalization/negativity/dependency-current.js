// Decorative dependency traversal; it never changes proof status or semantic edges.
export function installDependencyCurrent({nodes,graph,svg,selected,spatialHost,english}) {
  const ns='http://www.w3.org/2000/svg',byId=new Map(nodes.map(n=>[n.id,n]));
  const stylesheet=document.createElement('link');stylesheet.rel='stylesheet';
  stylesheet.href=new URL('./dependency-current.css?v=20261002-continuous-1',import.meta.url).href;
  document.head.append(stylesheet);
  const note=document.createElement('span');note.className='dependency-current-note';
  note.textContent=english?'Flow: premise → result':'流光：前提 → 结论';
  note.title=english?'Dependency traversal only. Proof status comes from the badges; open inputs stop the flow.':'流光展示依赖方向。验证状态看徽章；未完成输入会阻断流光。';
  window.addEventListener('languagechange',e=>{note.textContent=e.detail.english?'Flow: premise → result':'流光：前提 → 结论';note.title=e.detail.english?'Dependency traversal only. Proof status comes from the badges; open inputs stop the flow.':'流光展示依赖方向。验证状态看徽章；未完成输入会阻断流光。';});
  document.querySelector('.relation-legend').append(note);
  const spatialStage=spatialHost.querySelector('.spatial-stage');
  const spatialOverlay=document.createElementNS(ns,'svg');
  spatialOverlay.classList.add('dependency-current-spatial');spatialOverlay.setAttribute('aria-hidden','true');
  spatialStage.insertBefore(spatialOverlay,spatialStage.querySelector('.spatial-cards'));
  const reduced=matchMedia('(prefers-reduced-motion: reduce)');
  const pulses=new Map(),halos=new Map(),blockers=new Map();let frame=0,epoch=0,lastSelection='';
  const proven=id=>['done','conditional'].includes(byId.get(id)?.status);
  function chain(id,result=new Set()) {if(result.has(id))return result;result.add(id);byId.get(id).deps.forEach(p=>chain(p,result));return result;}
  function schedule(){if(!frame)frame=requestAnimationFrame(refresh);}
  function cancel(record){record.animations.forEach(a=>a.cancel());record.animations=[];}
  function remove(map,key){const record=map.get(key);cancel(record);if(record.originals&&!record.ownedWire)record.originals.forEach(e=>{if(e.getAttribute('mask')==='url(#'+record.mask.id+')')e.removeAttribute('mask');});record.elements.forEach(e=>e.remove());map.delete(key);}
  function keyframes(start,end,period,from,to){
    const a=start/period,b=end/period,fade=Math.min(140,(end-start)/4)/period;
    return [{offset:0,opacity:0,strokeDashoffset:from},
      {offset:a,opacity:0,strokeDashoffset:from},
      {offset:a+fade,opacity:1,strokeDashoffset:String(Number(from)+(Number(to)-Number(from))*fade/(b-a))},
      {offset:b-fade,opacity:1,strokeDashoffset:String(Number(to)-(Number(to)-Number(from))*fade/(b-a))},
      {offset:b,opacity:0,strokeDashoffset:to},
      {offset:1,opacity:0,strokeDashoffset:to}];
  }
  function animatePulse(record,signature,start,end,period){
    if(record.signature===signature)return;
    cancel(record);record.signature=signature;
    record.elements.forEach(e=>e.classList.toggle('dependency-current-static',reduced.matches));
    if(reduced.matches)return;
    record.animations=record.elements.map(e=>e.animate(keyframes(start,end,period,'12','-100'),
      {duration:period,iterations:Infinity,easing:'linear'}));
    record.animations.forEach(a=>a.startTime=epoch);
  }
  function syncHalo(key,card,signature,arrival,departure,period,terminal){
    let record=halos.get(key);
    if(!record){const e=document.createElement('span');e.className='dependency-current-halo';e.setAttribute('aria-hidden','true');
      const border=document.createElementNS(ns,'svg');border.classList.add('dependency-card-border');
      const paths=[];
      for(const route of ['upper','lower','orbit'])for(const layer of ['soft','core']){
        const path=document.createElementNS(ns,'path');path.classList.add('dependency-card-'+layer);
        path.dataset.route=route;path.setAttribute('pathLength','100');border.append(path);paths.push(path);
      }
      const rim=document.createElement('span');rim.className='dependency-orbit-rim';
      const merge=document.createElementNS(ns,'circle');merge.classList.add('dependency-card-merge');merge.setAttribute('r','1.7');border.append(merge);
      e.append(border,rim);card.append(e);record={elements:[e],border,rim,paths,merge,animations:[],signature:''};halos.set(key,record);
    }
    const w=card.clientWidth,h=card.clientHeight;if(!w||!h)return;
    const css=getComputedStyle(card),r=Math.min(parseFloat(css.borderTopLeftRadius)||16,w/2-1,h/2-1),p=.75;
    const unit=parseFloat(css.getPropertyValue(key.startsWith('2d:')?'--node-unit':'--card-unit'))||1;
    const port=key.startsWith('2d:')?(card.classList.contains('compact-input')?24:64)*unit:h/2;
    const input=Math.max(r,Math.min(h-r,port)),output=input;
    const upper=`M ${p} ${input} L ${p} ${r} Q ${p} ${p} ${r} ${p} L ${w-r} ${p} Q ${w-p} ${p} ${w-p} ${r} L ${w-p} ${output}`;
    const lower=`M ${p} ${input} L ${p} ${h-r} Q ${p} ${h-p} ${r} ${h-p} L ${w-r} ${h-p} Q ${w-p} ${h-p} ${w-p} ${h-r} L ${w-p} ${output}`;
    const orbit=upper+` L ${w-p} ${h-r} Q ${w-p} ${h-p} ${w-r} ${h-p} L ${r} ${h-p} Q ${p} ${h-p} ${p} ${h-r} L ${p} ${input} Z`;
    record.border.setAttribute('viewBox',`0 0 ${w} ${h}`);
    record.paths.forEach(path=>{const route=path.dataset.route,d={upper,lower,orbit}[route];if(path.getAttribute('d')!==d)path.setAttribute('d',d);
      path.style.display=terminal?'none':(route==='orbit'?'none':'');
    });
    record.rim.style.display=terminal?'':'none';
    const geometry=[w,h,r,input].join(':');
    if(record.rimGeometry!==geometry){
      // Map constant arc speed to angle; a single continuous gradient paints the whole rim.
      // Opposite rays meet opposite points of this symmetric outline, exactly half a perimeter apart.
      const probe=record.paths.find(path=>path.dataset.route==='orbit'),length=probe.getTotalLength();
      let previous;
      record.rimFrames=Array.from({length:97},(_,i)=>{
        const point=probe.getPointAtLength(length*i/96);
        let angle=Math.atan2(point.y-h/2,point.x-w/2)*180/Math.PI+90;
        if(previous===undefined&&angle<0)angle+=360;
        if(previous!==undefined){while(angle<previous-180)angle+=360;while(angle>previous+180)angle-=360;}
        previous=angle;return {offset:i/96,'--dependency-flow-angle':(angle-180)+'deg'};
      });
      record.rimGeometry=geometry;
      if(record.rim.getAnimations().length)record.rim.getAnimations()[0].effect.setKeyframes(record.rimFrames);
    }
    record.merge.setAttribute('cx',w-p);record.merge.setAttribute('cy',output);record.merge.style.display=terminal?'none':'';
    record.elements[0].dataset.flowMode=terminal?'orbit':'transit';
    record.elements[0].dataset.arrival=arrival;record.elements[0].dataset.departure=departure;
    if(record.signature===signature)return;
    cancel(record);record.signature=signature;
    if(reduced.matches)return;
    if(terminal){
      record.animations=[record.elements[0].animate([{opacity:0},{opacity:1}],
        {delay:arrival,duration:400,fill:'forwards',easing:'ease-out'}),
        record.rim.animate(record.rimFrames,
          {delay:arrival,duration:12000,iterations:Infinity,easing:'linear'})];
    }else{
      const a=arrival/period,b=departure/period,c=Math.min(.999,(departure+340)/period),rise=(arrival+160)/period;
      record.animations=[record.elements[0].animate([{offset:0,opacity:0},{offset:a,opacity:0},
        {offset:rise,opacity:.9,easing:'ease-out'},{offset:b,opacity:.8,easing:'ease-out'},
        {offset:c,opacity:0},{offset:1,opacity:0}],{duration:period,iterations:Infinity,easing:'linear'})];
      record.paths.filter(path=>path.dataset.route!=='orbit').forEach(path=>{
        path.style.strokeDasharray='12 112';
        record.animations.push(path.animate(keyframes(arrival,departure,period,'12','-100'),
          {duration:period,iterations:Infinity,easing:'linear'}));
      });
      record.animations.push(record.merge.animate([{offset:0,opacity:0},
        {offset:(departure-160)/period,opacity:0,easing:'ease-out'},{offset:b,opacity:1,easing:'ease-out'},
        {offset:(departure+280)/period,opacity:0},{offset:1,opacity:0}],{duration:period,iterations:Infinity,easing:'linear'}));
    }
    record.animations.forEach(a=>a.startTime=epoch);
  }
  function makePulse(key,parent){
    let record=pulses.get(key);if(record)return record;
    const elements=['glow','core'].map(layer=>{const p=document.createElementNS(ns,'path');
      p.classList.add('dependency-current-'+layer);p.setAttribute('pathLength','100');
      p.setAttribute('aria-hidden','true');parent.append(p);return p;});
    record={elements,animations:[],signature:''};pulses.set(key,record);return record;
  }
  function syncBlocker(key,edge,parent,d){
    let r=blockers.get(key);
    if(!r){const g=document.createElementNS(ns,'g');g.classList.add('dependency-current-blocker');
      const mask=document.createElementNS(ns,'mask');mask.id='wire-break-'+key.replace(/[^a-z0-9_-]/gi,'-');
      mask.setAttribute('maskUnits','userSpaceOnUse');mask.setAttribute('maskContentUnits','userSpaceOnUse');mask.setAttribute('mask-type','luminance');
      const white=document.createElementNS(ns,'rect');white.setAttribute('fill','white');
      const gap=document.createElementNS(ns,'path');gap.setAttribute('fill','none');gap.setAttribute('stroke','black');gap.setAttribute('stroke-linecap','butt');mask.append(white,gap);parent.append(mask);
      const probe=document.createElementNS(ns,'path');probe.setAttribute('fill','none');probe.setAttribute('stroke','none');g.append(probe);
      const casing=document.createElementNS(ns,'path'),strands=document.createElementNS(ns,'path'),shine=document.createElementNS(ns,'path');
      casing.classList.add('fracture-casing');strands.classList.add('fracture-strands');shine.classList.add('fracture-shine');g.append(casing,strands,shine);
      const aura=document.createElementNS(ns,'circle'),port=document.createElementNS(ns,'circle');
      aura.classList.add('blocked-charge');port.classList.add('blocked-port');g.append(aura,port);parent.append(g);
      const ownedWire=key.startsWith('3d:');let originals;
      if(ownedWire){originals=['shadow','metal','highlight'].map(layer=>{const p=document.createElementNS(ns,'path');p.classList.add('broken-wire-'+layer);parent.insertBefore(p,g);return p;});}
      else originals=[...parent.children].filter(e=>e.matches('.edge,.wire-shadow,.wire-highlight'));
      parent.append(g);originals.forEach(e=>e.setAttribute('mask','url(#'+mask.id+')'));
      r={elements:[g,mask,...(ownedWire?originals:[])],probe,casing,strands,shine,aura,port,mask,white,gap,originals,ownedWire,animations:[],signature:''};blockers.set(key,r);
    }
    const unit=parseFloat(getComputedStyle(graph).getPropertyValue('--node-unit'))||1;
    const factor=(parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--node-base-font'))||18)/16;
    const scale=key.startsWith('2d:')?unit/factor:1,geometry=d+':'+scale;
    if(r.geometry!==geometry){r.geometry=geometry;r.probe.setAttribute('d',d);r.gap.setAttribute('d',d);
      const length=r.probe.getTotalLength(),mid=length/2,half=Math.min(length*.16,11/scale),lo=mid-half,hi=mid+half;
      r.elements[0].dataset.cutFraction='0.5';r.elements[0].dataset.cutStart=lo;r.elements[0].dataset.cutEnd=hi;
      r.gap.setAttribute('stroke-width',12/scale);r.gap.setAttribute('stroke-dasharray',`0 ${lo} ${hi-lo} ${length+1}`);
      const box=r.probe.getBBox(),pad=18/scale;
      for(const e of [r.mask,r.white]){e.setAttribute('x',box.x-pad);e.setAttribute('y',box.y-pad);e.setAttribute('width',Math.max(1,box.width)+2*pad);e.setAttribute('height',Math.max(1,box.height)+2*pad);}
      if(r.ownedWire)r.originals.forEach(e=>e.setAttribute('d',d));
      let shell='',copper='',highlight='';
      [lo,hi].forEach((at,index)=>{
        const p=r.probe.getPointAtLength(at),before=r.probe.getPointAtLength(Math.max(0,at-1)),after=r.probe.getPointAtLength(Math.min(length,at+1));
        const n=Math.hypot(after.x-before.x,after.y-before.y)||1,ux=(after.x-before.x)/n,uy=(after.y-before.y)/n,nx=-uy,ny=ux,dir=index===0?1:-1;
        const point=(forward,side)=>`${p.x+(ux*forward+nx*side)/scale} ${p.y+(uy*forward+ny*side)/scale}`;
        shell+=`M ${point(-dir*.6,-1.5)} L ${point(dir*.6,1.5)} `;
        highlight+=`M ${point(-dir*.7,-1.5)} L ${point(dir*.15,-.2)} `;
        for(let k=-1;k<=1;k++)copper+=`M ${point(0,k*.7)} Q ${point(dir*2.5,k*.7+.45)} ${point(dir*(4.5+(k+1)*.45),k*.7+(index===0?1:-1)*.8)} `;
        if(index===0){[r.aura,r.port].forEach(e=>{e.setAttribute('cx',p.x);e.setAttribute('cy',p.y);});}
      });
      r.casing.setAttribute('d',shell);r.strands.setAttribute('d',copper);r.shine.setAttribute('d',highlight);
      r.aura.setAttribute('r',5/scale);r.port.setAttribute('r',1.25/scale);
    }
    if(r.signature!==String(reduced.matches)){cancel(r);r.signature=String(reduced.matches);
      if(!reduced.matches)r.animations=[r.aura.animate([{opacity:.18,transform:'scale(.85)'},{opacity:.48,transform:'scale(1.1)'},{opacity:.18,transform:'scale(.85)'}],
        {duration:2400,iterations:Infinity,easing:'ease-in-out'})];
    }
  }
  function refresh(){frame=0;const id=selected(),ancestors=chain(id),ready=new Map();
    if(lastSelection!==id){epoch=document.timeline.currentTime;lastSelection=id;}
    function complete(key){if(ready.has(key))return ready.get(key);
      const ok=proven(key)&&byId.get(key).deps.every(complete);ready.set(key,ok);return ok;}
    ancestors.forEach(complete);
    const keepPulses=new Set(),keepHalos=new Set(),keepBlockers=new Set();
    svg.querySelectorAll('.dependency-blocked-link').forEach(e=>e.classList.remove('dependency-blocked-link'));
    for(const view of ['2d','3d']){
      const cards=new Map(nodes.map(n=>[n.id,view==='2d'?graph.querySelector(`[data-node="${n.id}"]`):spatialHost.querySelector(`[data-spatial-node="${n.id}"]`)]));
      const visible=key=>ancestors.has(key)&&cards.get(key)&&!cards.get(key).hidden;
      const ranks=new Map();function rank(key){if(!ranks.has(key))ranks.set(key,Math.max(-1,...byId.get(key).deps.filter(visible).map(rank))+1);return ranks.get(key);}
      const routes=[...svg.querySelectorAll('.edge')].filter(edge=>visible(edge.dataset.from)&&visible(edge.dataset.to)&&
        ready.get(edge.dataset.from)&&ready.get(edge.dataset.to)&&edge.classList.contains('active')&&
        (view==='3d'?document.querySelector('#scope').value!=='open':edge.style.display!=='none'&&edge.parentElement.style.display!=='none')&&
        !(view==='3d'&&spatialHost.querySelector('[data-camera="direct"]').getAttribute('aria-pressed')==='true'&&edge.dataset.to!==id));
      const hop=1700,dwell=900,maximum=Math.max(1,...routes.map(e=>rank(e.dataset.to))),period=Math.max(3000,maximum*hop+dwell+1800);
      const stageBox=spatialStage.getBoundingClientRect();
      if(view==='3d'){spatialOverlay.setAttribute('viewBox',`0 0 ${Math.max(1,stageBox.width)} ${Math.max(1,stageBox.height)}`);}
      for(const edge of svg.querySelectorAll('.edge')){
        const from=edge.dataset.from,to=edge.dataset.to;
        if(!visible(from)||!visible(to)||proven(from)||!edge.classList.contains('active')||
          document.querySelector('#scope').value==='open'||
          view==='2d'&&edge.parentElement.style.display==='none'||
          view==='3d'&&spatialHost.querySelector('[data-camera="direct"]').getAttribute('aria-pressed')==='true'&&to!==id)continue;
        const key=view+':blocked:'+from+':'+to;keepBlockers.add(key);
        let d=edge.getAttribute('d');
        if(view==='2d')edge.parentElement.classList.add('dependency-blocked-link');
        else {const a=cards.get(from).getBoundingClientRect(),b=cards.get(to).getBoundingClientRect();
          const dx=b.x+b.width/2-a.x-a.width/2,dy=b.y+b.height/2-a.y-a.height/2;
          const t=Math.min(a.width/2/Math.max(.01,Math.abs(dx)),a.height/2/Math.max(.01,Math.abs(dy)));
          d=`M ${a.x+a.width/2+dx*t-stageBox.x} ${a.y+a.height/2+dy*t-stageBox.y} L ${b.x+b.width/2-stageBox.x} ${b.y+b.height/2-stageBox.y}`;
        }
        syncBlocker(key,edge,view==='2d'?edge.parentElement:spatialOverlay,d);
      }
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
        const end=rank(to)*hop,start=rank(from)*hop+dwell;
        animatePulse(record,[id,reduced.matches,start,end,period].join(':'),start,end,period);
      });
      involved.forEach(key=>{
        const card=cards.get(key),arrival=rank(key)*hop,haloKey=view+':'+key;
        keepHalos.add(haloKey);syncHalo(haloKey,card,[id,reduced.matches,arrival,period,key===id].join(':'),arrival,arrival+dwell,period,key===id);
      });
    }
    [...pulses.keys()].filter(k=>!keepPulses.has(k)).forEach(k=>remove(pulses,k));
    [...halos.keys()].filter(k=>!keepHalos.has(k)).forEach(k=>remove(halos,k));
    [...blockers.keys()].filter(k=>!keepBlockers.has(k)).forEach(k=>remove(blockers,k));
    pauseHiddenViews();
  }
  function pauseHiddenViews(){for(const [key,record] of [...pulses,...halos,...blockers]){
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
  const resize=new ResizeObserver(schedule);resize.observe(spatialStage);resize.observe(graph.closest('.graph-scroll'));
  window.addEventListener('atlasgeometrychange',schedule);
  window.addEventListener('typographychange',schedule);
  document.addEventListener('visibilitychange',pauseHiddenViews);
  reduced.addEventListener('change',schedule);
  schedule();
}
