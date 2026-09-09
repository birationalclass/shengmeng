// Three views of the same filtered-complex construction. No map K -> H(K) is implied.
export function createKToELab({viewport,controls,board,math,language}){
 const R=String.raw,choose=(zh,en)=>language()==='en'?en:zh;
 let active=false,design='quotient',step=0,context=null,renderKey='';
 const host=document.createElement('div');host.id='kePanel';host.hidden=true;viewport.append(host);
 const toolbar=document.createElement('div');toolbar.id='keControls';controls.prepend(toolbar);
 const L=(x,y,tex,cls='',w=190)=>`<div class="ke-math ${cls}" style="left:${x}px;top:${y}px;width:${w}px">${math(tex)}</div>`;
 const text=(x,y,zh,en,cls='',w=300)=>`<div class="ke-text ${cls}" style="left:${x}px;top:${y}px;width:${w}px">${choose(zh,en)}</div>`;
 const line=(x,y,x1,y1,cls='')=>`<path class="ke-arrow ${cls}" d="M${x},${y} L${x1},${y1}" marker-end="url(#ke-arrowhead)"/>`;
 const box=(x,y,tex,cls='',w=100)=>L(x,y,tex,`ke-node ${cls}`,w);
 const svg=body=>`<svg class="ke-lines" viewBox="0 0 840 525" aria-hidden="true"><defs><marker id="ke-arrowhead" markerWidth="9" markerHeight="9" refX="7" refY="4.5" orient="auto"><path d="m2 1.5 5 3-5 3" fill="none" stroke="#a5c6d7" stroke-width="1.3"/></marker></defs>${body}</svg>`;
 function quotient(){
  let labels='',paths='';for(let i=0;i<=3;i++)for(let j=0;j<=3;j++){const chosen=i+j===3&&i>=1,kept=i===1&&j===2;labels+=box(85+i*86,359-j*78,`K^{${i},${j}}`,`${chosen?'kept-source':'context-node'} ${kept?'projection-term':''}`,72);}
  // This band denotes a direct sum of spaces, not a set of individual vectors.
  paths+='<path class="ke-band" d="M145 180 Q154 168 168 181 L367 361 Q379 374 365 389 Q353 402 339 389 L142 211 Q129 197 145 180Z"/>';
  paths+=line(409,235,490,235,'phase-one projection-map');
  labels+=L(234,80,R`F^1C^3=K^{1,2}\oplus F^2C^3`,'',365);
  labels+=L(616,64,R`E_0^{1,2}:=F^1C^3/F^2C^3`,'phase-one result-label',318);
  labels+=box(616,237,R`E_0^{1,2}\cong K^{1,2}`,'phase-one quotient-target',243);
  labels+=L(448,212,R`\pi_1`,'phase-one projection-map',50);
  paths+=line(616,210,616,155,'phase-two');
  labels+=box(616,127,R`E_0^{1,3}`,'phase-two',135)+L(653,183,'d_0','phase-two',46);
  labels+=L(616,300,R`d_0\leftrightarrow\delta_2`,'phase-two differential-note',220);
  labels+=`<div class="ke-subquotient phase-three" style="left:479px;top:335px;width:274px"><div>${math(R`Z:=\ker\delta_2`)}</div><div class="ke-boundary">${math(R`B:=\operatorname{im}\delta_2\subseteq Z`)}</div><div>${math(R`E_1^{1,2}=Z/B`)}</div></div>`;
  labels+=text(232,447,'原来的 K 各项始终保留','The original K terms remain visible','quiet',350);
  return svg(paths)+labels;
 }
 function layers(){
  let labels='',paths='';const origins=[[55,117],[305,117],[555,117]],names=['K','E_0','E_1'];
  for(let k=0;k<3;k++){
   const [x,y]=origins[k],visibility=k===0?'':k===1?'phase-one':'phase-three';
   paths+=`<g class="${visibility}"><path class="ke-sheet sheet-${k}" d="M${x},${y+53} L${x+189},${y} L${x+204},${y+273} L${x+15},${y+326}Z"/></g>`;
   labels+=L(x+106,80,names[k],`${visibility} sheet-title`,130);
   for(let i=0;i<3;i++)for(let j=1;j<=3;j++){
    const nx=x+41+i*63+(3-j)*4,ny=y+264-(j-1)*75-i*17;
    labels+=L(nx,ny,`${names[k]}^{${i},${j}}`,`${visibility} layer-term ${i===1&&j===2?'layer-picked':''}`,66);
    if(k<2&&i===1&&j<3){paths+=line(nx,ny-17,nx-4,ny-55,`phase-two layer-map layer-map-${k}`);labels+=L(nx+25,ny-39,k===0?R`\delta_2`:'d_0','phase-two layer-map-label',38);}
   }
  }
  labels+=L(281,264,R`\cong`,'phase-one layer-identification',46);
  labels+=L(523,265,R`H^{\bullet}`,'phase-three',68);
  labels+=text(420,477,'自然识别与取上同调是两种不同的操作','Natural identification and cohomology are different operations','quiet',700);
  return svg(paths)+labels;
 }
 function local(){
  let paths=line(194,354,194,292,'local-delta')+line(194,220,194,158,'local-delta');
  paths+=line(274,257,395,257,'phase-one local-identification');
  let labels=L(194,57,R`K^{1,\bullet}`,'sheet-title',160);
  labels+=box(194,125,R`K^{1,3}`,'',132)+box(194,257,R`K^{1,2}`,'projection-term',132)+box(194,389,R`K^{1,1}`,'',132);
  labels+=L(232,191,R`\delta_2`,'',55)+L(232,323,R`\delta_2`,'',55);
  labels+=L(571,109,R`E_0^{1,2}:=F^1C^3/F^2C^3`,'phase-one',365);
  labels+=box(571,257,R`E_0^{1,2}\cong K^{1,2}`,'phase-one quotient-target',300);
  labels+=L(336,236,R`\cong`,'phase-one local-identification',62);
  labels+=L(571,176,R`d_0^{1,2}=\delta_2^{1,2}`,'phase-two differential-note',315);
  labels+=`<div class="ke-subquotient phase-three" style="left:397px;top:321px;width:351px"><div>${math(R`Z=\ker(\delta_2:K^{1,2}\to K^{1,3})`)}</div><div class="ke-boundary">${math(R`B=\operatorname{im}(\delta_2:K^{1,1}\to K^{1,2})`)}</div><div>${math(R`Z\twoheadrightarrow E_1^{1,2}=Z/B`)}</div></div>`;
  labels+=text(194,470,'先识别 E₀，再对整列求上同调','Identify E₀, then take column cohomology','quiet',330);
  return svg(paths)+labels;
 }
 function exposition(){
  const formulas=[
   [R`C^3:=\operatorname{Tot}^3K,\qquad F^1C^3=K^{1,2}\oplus F^2C^3`,R`F^2C^3=K^{2,1}\oplus K^{3,0}`],
   [R`\pi_1:F^1C^3\longrightarrow K^{1,2},\quad\ker\pi_1=F^2C^3`,R`E_0^{1,2}:=F^1C^3/F^2C^3\xrightarrow{\sim}K^{1,2}`],
   [R`d_0:E_0^{1,2}\longrightarrow E_0^{1,3},\qquad d_0[a]=[Da]`,R`D=\delta_1+\delta_2\quad\Longrightarrow\quad d_0^{1,2}\leftrightarrow\delta_2^{1,2}`],
   [R`E_1^{1,2}=H^2(K^{1,\bullet},\delta_2)`,R`=\frac{\ker(\delta_2:K^{1,2}\to K^{1,3})}{\operatorname{im}(\delta_2:K^{1,1}\to K^{1,2})}`]
  ];
  const notes=[
   choose('固定位置 (p,q)=(1,2)，n=3。图中各项是一般向量空间；图形大小不表示维数。','Fix (p,q)=(1,2), n=3. Terms are general vector spaces; shapes do not encode dimensions.'),
   choose('同构由取第 1 列分量诱导，无需选择补空间。更高列分量仅在这个商中为零。','Projection to column 1 induces the isomorphism, with no choice of complement. Higher-column components vanish only in this quotient.'),
   choose('δ₁ 提高列指标，在目标关联分次中为零；δ₂ 保持列指标，诱导 d₀。等号是在上述自然识别下理解的。','The horizontal δ₁ raises the column and vanishes in the target graded quotient; δ₂ preserves it and induces d₀, under the natural identification.'),
   choose('δ₂²=0 保证 im δ₂ ⊆ ker δ₂。只有闭元素才能表示 E₁ 的类；一般没有从整个 K¹² 到 E₁¹² 的自然商映射。','Since δ₂²=0, im δ₂ lies in ker δ₂. Only cocycles represent E₁ classes; there is generally no natural quotient map from all of K¹² to E₁¹².')
  ];
  return `<div class="operation-content ke-exposition">${formulas[step].map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}</div><p class="operation-note">${notes[step]}</p>`;
 }
 function paint(){
  if(!context)return;
  const eligible=!context.cover&&(context.module==='initial'&&context.initialReveal>=0||context.module==='learn');
  toolbar.hidden=!eligible;if(!eligible)active=false;
  host.hidden=!active;controls.classList.toggle('ke-controls-active',active);viewport.closest('.visual-column').classList.toggle('ke-active',active);
  toolbar.innerHTML=`<button data-ke-toggle aria-pressed="${active}">${active?choose('返回定义图','Back to definition'):choose('K → E · 三套方案','K → E · Three designs')}</button>${active?`<div class="ke-designs" role="group" aria-label="${choose('可视化方案','Visualization design')}">${[['quotient','① 滤过与投影','① Filtration'],['layers','② 分层对照','② Layers'],['local','③ 局部放大','③ Local view']].map(([id,zh,en])=>`<button data-ke-design="${id}" aria-pressed="${design===id}">${choose(zh,en)}</button>`).join('')}</div><div class="ke-steps" role="group" aria-label="${choose('构造步骤','Construction step')}">${['K','E_0','d_0','E_1'].map((tex,i)=>`<button data-ke-step="${i}" aria-pressed="${step===i}">${math(tex)}</button>`).join('')}</div>`:''}`;
  window.spectralTransition={active,design,step};
  if(!active)return;
  const key=design+language();
  if(renderKey!==key){host.innerHTML=`<div class="ke-canvas" data-design="${design}">${({quotient,layers,local})[design]()}</div>`;renderKey=key;}
  host.dataset.step=step;host.dataset.design=design;
  host.querySelectorAll('.phase-one,.phase-two,.phase-three').forEach(el=>{const required=el.classList.contains('phase-three')?3:el.classList.contains('phase-two')?2:1;el.classList.toggle('ke-visible',step>=required);el.setAttribute('aria-hidden',String(step<required));});
  // No arrow is ever drawn from the whole K-space to E1.
  host.querySelectorAll('.projection-map,.local-identification').forEach(el=>el.classList.toggle('ke-replaced',step===3));
  board.innerHTML=exposition();
  const scope=viewport.parentElement.querySelector('.diagram-scope');if(scope)scope.innerHTML=math(R`(p,q)=(1,2),\quad n=p+q=3`);
  fit();window.spectralTransition={active,design,step};
 }
 function fit(){const canvas=host.firstElementChild;if(!canvas)return;const r=viewport.getBoundingClientRect(),scale=Math.min(r.width/840,r.height/525);canvas.style.transform=`translate(-50%,-50%) scale(${scale})`;}
 new ResizeObserver(fit).observe(viewport);
 toolbar.addEventListener('click',e=>{const toggle=e.target.closest('[data-ke-toggle]'),d=e.target.closest('[data-ke-design]'),s=e.target.closest('[data-ke-step]');if(toggle)active=!active;if(d)design=d.dataset.keDesign;if(s)step=Number(s.dataset.keStep);paint();if(!active)controls.dispatchEvent(new CustomEvent('ke-close',{bubbles:true}));});
 return {sync(s){context=s;paint();},open(){active=true;step=0;paint();},close(){const wasActive=active;active=false;paint();if(wasActive)controls.dispatchEvent(new CustomEvent('ke-close',{bubbles:true}));},isActive:()=>active};
}
