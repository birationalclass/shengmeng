/* Membership regions, not sampled pixels: each highlighted region has an exact Boolean meaning. */
(()=>{
 'use strict';
 const parity=(a,b,c)=>(a!==b)!==c;
 const stages=['两个集合','只保留一侧','引入第三个集合','比较括号顺序','相同的结果'];
 const english=['Two sets','Keep either side','Introduce C','Compare bracketings','The same result'];
 const points=[[112,105],[206,105],[159,184]],colors=['#87b7cf','#dfa581','#a7c499'];
 let serial=0;
 function mount(root){
  const en=()=>window.CourseLanguage?.language==='en',t=(zh,eng)=>en()?eng:zh;
  const uid='xor-'+(++serial);let phase=0,timer=0,selected=7;
  root.innerHTML=`<section class="xor-lab" aria-label="${t('对称差结合律交互演示','Symmetric difference associativity demonstration')}"><header class="xor-heading"><span>SYMMETRIC DIFFERENCE</span><h4>${t('不同的顺序，同一片区域','Different paths. The same region.')}</h4><p>${t('△ 保留恰好属于一侧的点；重叠部分抵消。','△ keeps points belonging to exactly one operand; overlap cancels.')}</p></header><nav class="xor-stages" aria-label="${t('演示步骤','Demonstration steps')}">${stages.map((s,i)=>`<button type="button" data-xor-phase="${i}"><b>0${i+1}</b><span>${t(s,english[i])}</span></button>`).join('')}</nav><div class="xor-panels"><figure data-xor-side="0"></figure><figure data-xor-side="1"></figure></div><p class="xor-caption" aria-live="polite"></p><div class="xor-controls"><button type="button" data-xor-prev aria-label="${t('上一步','Previous step')}">←</button><button type="button" data-xor-play></button><button type="button" data-xor-next aria-label="${t('下一步','Next step')}">→</button><span class="xor-counter"></span></div><div class="xor-inspector" hidden><p>${t('逐点检验 · 选择恰好属于的集合','Pointwise check · Select exact membership')}</p><div class="xor-memberships">${[1,2,4,3,5,6,7,0].map(bits=>`<button type="button" data-xor-bits="${bits}">${bits?t('仅 ','Only ')+['A','B','C'].filter((_,i)=>bits&(1<<i)).join(', '):t('都不属于','Outside all')}</button>`).join('')}</div><output class="xor-verdict"></output></div><p class="xor-footnote">${t('圆形仅示意归属关系。证明对有限集、无限集同样成立。','Circles illustrate membership only. The proof applies to finite and infinite sets alike.')}</p></section>`;
  const label=[
   ['先观察 A 与 B 的交叠。','Start with the overlap of A and B.'],
   ['两边的月牙区域留下，交叠部分消失：这就是 A △ B。','Keep the two crescents and remove the overlap: this is A △ B.'],
   ['引入 C。左边先算 A △ B；右边先算 B △ C。','Introduce C. Compute A △ B on the left and B △ C on the right.'],
   ['金色是先算出的集合。下一次 △ 将反转另一集合内每一点的保留状态。','Gold marks the intermediate set. The next △ toggles membership inside the remaining set.'],
   ['两边都恰好保留属于 1 个或 3 个集合的点；中央三重交叠也保留。','Both retain points in exactly one or three sets, including the central triple overlap.']
  ];
  function circle(i,attrs=''){return `<circle cx="${points[i][0]}" cy="${points[i][1]}" r="76" ${attrs}/>`;}
  function diagram(side){
   const prefix=uid+'-'+side,three=phase>=2,count=three?3:2;
   const defs=points.map((_,i)=>`<clipPath id="${prefix}-c${i}">${circle(i)}</clipPath>`).join('');
   let regions='';
   for(let bits=1;bits<(1<<count);bits++){
    const a=!!(bits&1),b=!!(bits&2),c=!!(bits&4);
    const active=phase===0?false:phase>=4?parity(a,b,c):side===0||phase===1?a!==b:b!==c;
    const mask=prefix+'-m'+bits;
    let region=`<rect width="320" height="280" mask="url(#${mask})" fill="${active?'#d8b469':'currentColor'}" opacity="${active?'.8':'.035'}"/>`;
    for(let i=0;i<count;i++)if(bits&(1<<i))region=`<g clip-path="url(#${prefix}-c${i})">${region}</g>`;
    regions+=`<mask id="${mask}" maskUnits="userSpaceOnUse" x="0" y="0" width="320" height="280"><rect width="320" height="280" fill="white"/>${points.map((_,i)=>i<count&&!(bits&(1<<i))?circle(i,'fill="black"'):'').join('')}</mask><g data-region="${bits}" data-in-result="${active}">${region}</g>`;
   }
   const expression=phase<2?(phase===0?'A, B':'A △ B'):side===0?'(A △ B) △ C':'A △ (B △ C)';
   return `<figcaption><span>${t(side?'路线二':'路线一',side?'PATH TWO':'PATH ONE')}</span><strong>${expression}</strong></figcaption><svg viewBox="0 0 320 280" role="img" aria-label="${expression}"><defs>${defs}</defs>${regions}${points.map((_,i)=>`<g class="xor-circle" style="opacity:${i<count?1:0}">${circle(i,`fill="none" stroke="${colors[i]}" stroke-width="${phase===3&&i===(side===0?2:0)?3:1.5}" ${phase===3&&i===(side===0?2:0)?'stroke-dasharray="5 5"':''}`)}<text x="${[66,250,159][i]}" y="${[44,44,274][i]}" text-anchor="middle" fill="${colors[i]}">${['A','B','C'][i]}</text></g>`).join('')}</svg>`;
  }
  function inspect(){
   const a=!!(selected&1),b=!!(selected&2),c=!!(selected&4),left=Number((a!==b)!==c),right=Number(a!==(b!==c));
   root.querySelectorAll('[data-xor-bits]').forEach(button=>button.setAttribute('aria-pressed',String(+button.dataset.xorBits===selected)));
   root.querySelector('.xor-verdict').textContent=`(${+a} + ${+b}) + ${+c} ≡ ${+a} + (${+b} + ${+c}) ≡ ${left} (mod 2) · ${left===right&&left?t('保留','KEEP'):t('抵消 / 不保留','EXCLUDE')}`;
  }
  function draw(){
   root.querySelector('.xor-lab').dataset.phase=phase;
   root.querySelectorAll('[data-xor-side]').forEach((panel,i)=>{panel.innerHTML=diagram(i);if(!matchMedia('(prefers-reduced-motion: reduce)').matches){panel.querySelectorAll('[data-in-result=true]').forEach(region=>region.animate?.([{opacity:.2},{opacity:1}],{duration:600,easing:'cubic-bezier(.2,0,0,1)'}));if(phase===2)panel.querySelector('.xor-circle:last-child')?.animate?.([{opacity:0,transform:'translateY(12px)'},{opacity:1,transform:'translateY(0)'}],{duration:650,easing:'cubic-bezier(.2,0,0,1)'});}});
   root.querySelectorAll('[data-xor-phase]').forEach(button=>{button.setAttribute('aria-current',+button.dataset.xorPhase===phase?'step':'false');button.classList.toggle('is-complete',+button.dataset.xorPhase<phase);});
   root.querySelector('.xor-caption').textContent=t(...label[phase]);root.querySelector('.xor-counter').textContent=`${phase+1} / 5`;
   root.querySelector('[data-xor-prev]').disabled=phase===0;root.querySelector('[data-xor-next]').disabled=phase===4;
   root.querySelector('[data-xor-play]').textContent=timer?t('Ⅱ 暂停','Ⅱ Pause'):phase===4?t('↻ 重播','↻ Replay'):t('▶ 播放演示','▶ Play');
   root.querySelector('.xor-inspector').hidden=phase!==4;inspect();
  }
  function stop(){clearTimeout(timer);timer=0;}
  function advance(){stop();if(!root.isConnected||!root.closest('details')?.open||document.hidden)return;phase++;if(phase<4)timer=setTimeout(advance,2600);draw();}
  root.addEventListener('click',event=>{const button=event.target.closest('button');if(!button)return;if(button.hasAttribute('data-xor-bits')){selected=+button.dataset.xorBits;inspect();return;}if(button.hasAttribute('data-xor-play')){if(timer)stop();else{if(phase===4)phase=0;timer=setTimeout(advance,2600);}}else{stop();phase=button.hasAttribute('data-xor-phase')?+button.dataset.xorPhase:Math.max(0,Math.min(4,phase+(button.hasAttribute('data-xor-next')?1:-1)));}draw();});
  root.closest('details')?.addEventListener('toggle',event=>{if(!event.target.open){stop();draw();}});
  draw();return()=>stop();
 }
 window.SymmetricDifference={mount,parity};
})();
