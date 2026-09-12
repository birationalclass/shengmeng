import {proofPanel,proofSections} from './proof-panel.js?v=109';
import {fitDiagramSurface} from './diagram-viewport.js?v=67';
import {replaceMathContent} from './math-transitions.js?v=97';
import {visualMotion} from './visual-style.js?v=41';

// A filtration of total cohomology, not a decomposition or a choice of basis.
// Every vertical map is an inclusion; only F^p H^n projects to its graded quotient.
export function createAbutmentView({viewport,board,controls,math,language}){
 const R=String.raw,t=(zh,en)=>language()==='en'?en:zh;
 const host=document.createElement('div');host.id='abutmentView';host.inert=true;host.setAttribute('aria-hidden','true');viewport.append(host);
 const toolbar=document.createElement('nav');toolbar.id='abutmentControls';toolbar.hidden=true;controls.append(toolbar);
 let active=false,context=null,n=3,p=1,key='';
 const label=(x,y,tex,width=240,kind='')=>`<span class="abutment-label ${kind}" style="left:${x-width/2}px;top:${y-22}px;width:${width}px">${math(tex)}</span>`;
 const formula=f=>`<div class="operation-equation">${math(f,true)}</div>`;
 const filtrationProof=[
  {name:['诱导滤过','Induced filtration'],f:[R`H^n:=H^n(C^\bullet,D)`,R`F^pH^n:=\operatorname{im}\!\left(H^n(F^pC^\bullet,D)\xrightarrow{H^n(\iota_p)} H^n\right)`],note:()=>t('使用子复形的包含映射在上同调上的像。这个映射未必单射，因此不能把其定义域直接当作滤过子空间。','Use the image of the map on cohomology induced by inclusion of subcomplexes. This map need not be injective, so its domain is not itself the filtration subspace.')},
  {name:['闭代表元','Closed representatives'],f:[R`Z^n:=\ker(D:C^n\to C^{n+1}),\quad B^n:=\operatorname{im}(D:C^{n-1}\to C^n)`,R`F^pH^n=\frac{(F^pC^n\cap Z^n)+B^n}{B^n}\subseteq H^n`,R`[a]_H\in F^pH^n\iff\exists z\in F^pC^n\cap Z^n:\ [a]_H=[z]_H`],note:()=>t('条件是存在该滤过中的闭代表元；原先选定的代表元本身未必在该滤过中。','The condition is the existence of a cocycle representative in the filtration; a previously chosen representative need not itself lie there.')},
  {name:['有限滤过','Finite filtration'],f:[R`H^n=F^0H^n\supseteq F^1H^n\supseteq\cdots\supseteq F^{n+1}H^n=0`,R`\operatorname{Gr}_F^pH^n:=F^pH^n/F^{p+1}H^n`],note:()=>t('第一象限给出 F⁰C•=C• 以及 Fⁿ⁺¹Cⁿ=0。图中的箭头是包含映射，各框大小不表示维数；相邻滤过项可以相等。','The first quadrant gives F⁰C•=C• and Fⁿ⁺¹Cⁿ=0. Arrows in the diagram are inclusions; box sizes do not encode dimensions, and adjacent filtration terms may coincide.')}
 ];
 const convergencePropertyProof=[
  {name:['稳定商','The stable quotient'],f:[R`n=p+q,\quad Z^n:=\ker D|_{C^n},\quad B^n:=D(C^{n-1})`,R`E_\infty^{p,q}\cong\frac{F^pC^n\cap Z^n}{(F^{p+1}C^n\cap Z^n)+(F^pC^n\cap B^n)}`],note:()=>t('当页数足够大时，滤过闭链条件成为 Da=0，而边界的来源包含全部 Cⁿ⁻¹。将这两点代入 2.1 的滤过商表示，得到该式。','For sufficiently large page number, the filtered cocycle condition becomes Da=0 and the allowed sources of boundaries include all of Cⁿ⁻¹. Substituting into the filtered-quotient model of 2.1 gives this expression.')},
  {name:['典范映射','The canonical map'],f:[R`\begin{aligned}\theta:F^pC^n\cap Z^n&\longrightarrow F^pH^n/F^{p+1}H^n\\a&\longmapsto[a]_H+F^{p+1}H^n\end{aligned}`,R`\ker\theta=(F^{p+1}C^n\cap Z^n)+(F^pC^n\cap B^n)`],note:()=>t('由诱导滤过的定义，θ 满射。θ(a)=0 当且仅当 a 与某个更高滤过中的闭元相差一个总边界；该边界也在 FᵖCⁿ 中。这给出所列核，再由第一同构定理得到收敛同构。','The definition of the induced filtration makes θ surjective. Its value is zero precisely when a differs from a cocycle in the next filtration by a total boundary, which then also lies in FᵖCⁿ. This identifies the kernel; the first isomorphism theorem gives the convergence isomorphism.')},
  {name:['逐层恢复','Reconstructing by filtration'],f:[R`0\longrightarrow F^{p+1}H^n\longrightarrow F^pH^n\longrightarrow E_\infty^{p,n-p}\longrightarrow0`],note:()=>t('沿总次数 n 的对角线，各稳定项给出 Hⁿ 的逐层滤过商。向量空间情形可以选择分裂，但收敛本身没有给出典范的直和分解。','Along total degree n, the stable terms give the successive filtration quotients of Hⁿ. Vector-space splittings can be chosen, but convergence itself supplies no canonical direct-sum decomposition.')}
 ];
 const notationProof=[
  {name:['起始页记号','Starting-page notation'],f:[R`E_{r_0}^{p,q}\Longrightarrow H^{p+q}`,R`\{(E_s^{\bullet,\bullet},d_s)\}_{s\ge r_0}\Longrightarrow H^\bullet`,R`E_2^{p,q}=H^p(Y,R^qf_*\mathcal F)\Longrightarrow H^{p+q}(X,\mathcal F)`],note:()=>t(`第一行用选定的起始页标示整条谱序列。Leray 谱序列在第二页有所示描述，之后仍须考虑 ${math('d_2,d_3,\\ldots')}；写 ${math('E_2')} 不表示第二页已经稳定。这里 ${math(R`\mathcal F`)} 是层，与滤过 ${math('F^p')} 不同。`,`The chosen starting page labels the spectral sequence. For the Leray spectral sequence, the displayed description is at page two; later differentials ${math('d_2,d_3,\\ldots')} still matter. Writing ${math('E_2')} does not assert stabilization there. The sheaf ${math(R`\mathcal F`)} is distinct from the filtration ${math('F^p')}.`),refs:'notation'}
 ];
 const degenerationProof=[
  {name:['收敛与退化','Convergence and degeneration'],f:[R`d_s=0\quad(\forall s\ge r_0)`,R`\Longrightarrow\quad E_{r_0}^{p,q}\cong E_{r_0+1}^{p,q}\cong\cdots\cong E_\infty^{p,q}`,R`E_\infty^{p,q}\cong\operatorname{Gr}_F^pH^{p+q}`],note:()=>t(`第一行是从第 ${math('r_0')} 页退化的额外条件。收敛本身不保证它成立；即使在 ${math('E_2')} 退化，也首先得到 ${math(R`E_2^{p,q}\cong\operatorname{Gr}_F^pH^{p+q}`)}，而不是 ${math(R`E_2^{p,q}\cong H^{p+q}`)}。`,`The first line is the additional condition for degeneration at page ${math('r_0')}. Convergence alone does not imply it. Even degeneration at ${math('E_2')} identifies its terms with the graded pieces of the target, not with the whole target.`),refs:'degeneration'}
 ];
 const referenceLink=(url,label)=>`<a href="${url}" target="_blank" rel="noopener">${label}</a>`;
 const mc='https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/McCleary-UGSS.pdf',weibel='https://math.mit.edu/~hrm/palestine/weibel/05-spectral_sequences.pdf';
 function references(entry){
  if(entry.refs==='definition')return referenceLink(mc+'#page=47','McCleary, Definition 2.4')+' · '+referenceLink(weibel+'#page=4','Weibel, 5.2.5');
  if(entry.refs==='notation')return referenceLink(weibel+'#page=4','Weibel, 5.2.3–5.2.5')+' · '+referenceLink(weibel+'#page=33','5.8.6 (Leray)');
  if(entry.refs==='degeneration')return referenceLink(mc+'#page=21','McCleary, Definition 1.3');
  return referenceLink(mc+'#page=47','McCleary, Theorem 2.6')+' · '+referenceLink(mc+'#page=62','Theorem 2.15');
 }
 function definitionExposition(){
  board.dataset.currentProofTopic='convergence-definition';board.dataset.currentProofStep='0';
  const family=math(R`\{(E_r^{\bullet,\bullet},d_r)\}_{r\ge0}`);
  replaceMathContent(board,`<div class="proof-body convergence-definition"><p class="operation-note">${t(`我们称第一象限上同调型谱序列 ${family} <strong>收敛到</strong>非负分次向量空间 ${math(R`H^\bullet`)}，<strong>如果</strong>对每个 ${math(R`n\ge0`)}，${math('H^n')} 配备有限递减滤过`,`We say that a first-quadrant cohomological spectral sequence ${family} <strong>converges to</strong> a nonnegatively graded vector space ${math(R`H^\bullet`)} <strong>if</strong>, for every ${math(R`n\ge0`)}, ${math('H^n')} is equipped with a finite decreasing filtration`)}</p>${formula(R`H^n=F^0H^n\supseteq F^1H^n\supseteq\cdots\supseteq F^{n+1}H^n=0`)}<p class="operation-note">${t(`并对所有 ${math(R`p,q\ge0`)} 给定同构`,`together with isomorphisms, for all ${math(R`p,q\ge0`)},`)}</p>${formula(R`E_\infty^{p,q}\cong\frac{F^pH^{p+q}}{F^{p+1}H^{p+q}}=\operatorname{Gr}_F^pH^{p+q}`)}</div><p class="operation-note proof-reference">${references({refs:'definition'})}</p>`);
 }
 function expositionTopic(){return context.step===2?'hfiltration':['definition','convergence','notation','degeneration'][context.notePage||0];}
 function exposition(){
  const topic=expositionTopic();if(topic==='definition'){definitionExposition();return;}
  const entries={hfiltration:filtrationProof,convergence:convergencePropertyProof,notation:notationProof,degeneration:degenerationProof}[topic],entry=entries[0];
  board.dataset.currentProofTopic=topic;delete board.dataset.currentProofStep;
  const summaries={
   hfiltration:{f:[R`[a]_H\in F^pH^n\iff\exists z\in F^pC^n:\ Dz=0,\ [a]_H=[z]_H`],note:t('要求存在该滤过中的闭代表元；原先选定的代表元未必在其中。','A cocycle representative in this filtration must exist; a previously chosen representative need not lie there.')},
   convergence:{f:[R`E_\infty^{p,q}\cong\operatorname{Gr}_F^pH^{p+q}(C^\bullet,D)`],note:t('将滤过中的闭元送到其上同调类，再对下一层滤过取商。该映射满射，核恰为稳定商的分母。','Send a filtered cocycle to its cohomology class modulo the next filtration. This map is surjective, with kernel equal to the denominator of the stable quotient.')},
   notation:{f:[notationProof[0].f[2]],note:t('E₂ 标示有明确描述的起始页，不表示第二页已经稳定。','E₂ labels the starting page with an explicit description; it does not assert stabilization on page two.')},
   degeneration:{f:degenerationProof[0].f.slice(0,2),note:t('退化是所有后续微分为零的额外条件，收敛本身不保证它成立。','Degeneration imposes the additional condition that every later differential vanish; convergence alone does not imply it.')}
  },summary=summaries[topic];
  replaceMathContent(board,proofPanel({key:'abutment-'+topic,title:t(...entries[0].name),formulas:summary.f,note:summary.note,details:proofSections(entries,{math,title:e=>t(...e.name),note:e=>e.note()})+`<p>${references(entry)}</p>`,math,language}));
 }
 function draw(){
  const y=i=>105+54*i,final=context.step===3,applied=context.step===2||context.notePage===1;
  let svg='<defs><marker id="abutment-tip" markerUnits="userSpaceOnUse" markerWidth="9" markerHeight="9" refX="7" refY="4.5" orient="auto"><path d="M1.5,1.5 L7,4.5 L1.5,7.5" fill="none" stroke="currentColor" stroke-width="1.3"/></marker></defs>',labels=label(420,42,applied?R`H^{${n}}:=H^{${n}}(C^\bullet,D)`:R`H^{${n}}`,420,'title');
  for(let i=0;i<=n+1;i++){
   const chosen=i===p||i===p+1,tex=i===0?`F^0H^{${n}}=H^{${n}}`:i===n+1?`F^{${i}}H^{${n}}=0`:`F^{${i}}H^{${n}}`;
   svg+=`<rect class="abutment-term ${chosen?'chosen':''}" data-filtration="${i}" x="125" y="${y(i)-19}" width="220" height="38" rx="9"/>`;
   labels+=label(235,y(i),tex,218,chosen?'gold':'');
   if(i>0)svg+=`<path class="abutment-inclusion" data-from="${i}" data-to="${i-1}" d="M235,${y(i)-21} V${y(i-1)+23}" marker-end="url(#abutment-tip)"/>`;
  }
  const selectedY=y(p);
  svg+=`<path class="abutment-projection" d="M355,${selectedY} H513" marker-end="url(#abutment-tip)"/><rect class="abutment-term quotient" x="525" y="${selectedY-24}" width="230" height="48" rx="10"/>`;
  labels+=label(435,selectedY-23,R`\pi`,65,'gold')+label(440,selectedY+28,R`\ker\pi=F^{${p+1}}H^{${n}}`,220,'small')+label(640,selectedY,R`\operatorname{Gr}_F^{${p}}H^{${n}}`,222,'gold');
  if(final){
   svg+=`<path class="abutment-isomorphism" d="M640,${selectedY+76} V${selectedY+29}" marker-end="url(#abutment-tip)"/><rect class="abutment-term stable" x="545" y="${selectedY+83}" width="190" height="42" rx="10"/>`;
   labels+=label(663,selectedY+54,R`\sim`,36,'gold')+label(640,selectedY+104,R`E_\infty^{${p},${n-p}}`,182,'blue');
  }
  const scene=document.createElement('div');scene.className='abutment-scene';scene.innerHTML=`<svg viewBox="0 0 840 525" role="img" aria-label="${t('总上同调的滤过与关联分次','Filtration and associated graded of total cohomology')}">${svg}</svg>${labels}`;
  for(const old of [...host.children]){
   old.setAttribute('aria-hidden','true');const opacity=getComputedStyle(old).opacity;old.getAnimations().forEach(a=>a.cancel());
   if(visualMotion().reduced)old.remove();else{const fade=old.animate([{opacity},{opacity:0}],{duration:visualMotion().exit,fill:'forwards',easing:visualMotion().easing});fade.finished.then(()=>old.remove(),()=>old.remove());}
  }
  host.append(scene);if(!visualMotion().reduced)scene.animate([{opacity:0},{opacity:1}],{duration:visualMotion().enter,easing:visualMotion().easing});
  window.spectralAbutment={active,n,p,q:n-p,showsStableTerm:final};
 }
 function paintControls(){toolbar.innerHTML=`<label>${math('n')} <input data-abutment-n type="range" min="0" max="4" value="${n}" aria-label="${t('总次数','Total degree')}"><output>${n}</output></label><label>${math('p')} <input data-abutment-p type="range" min="0" max="${n}" value="${p}" aria-label="${t('滤过指标','Filtration index')}"><output>${p}</output></label>`;}
 const fit=()=>fitDiagramSurface(viewport,host,'--abutment-scale');new ResizeObserver(fit).observe(viewport);
 toolbar.addEventListener('input',e=>{
  if(!active||!e.target.matches('[data-abutment-n],[data-abutment-p]'))return;
  if(e.target.matches('[data-abutment-n]')){n=Number(e.target.value);p=Math.min(p,n);const input=toolbar.querySelector('[data-abutment-p]');input.max=n;input.value=p;input.nextElementSibling.textContent=p;}else p=Number(e.target.value);
  e.target.nextElementSibling.textContent=e.target.value;draw();exposition();
 });

 return {sync(s){
  const wasActive=active;active=!s.cover&&s.module==='converge'&&s.step>=2;context=s;
  host.classList.toggle('is-active',active);host.inert=!active;host.setAttribute('aria-hidden',String(!active));toolbar.hidden=!active;viewport.classList.toggle('has-abutment-view',active);
  if(!active){key='';window.spectralAbutment={active:false};return;}
  if(!wasActive){n=s.n;p=Math.max(0,Math.min(s.p,n));}
  const next=[s.step,s.notePage,n,p,language()].join(':');if(next!==key){key=next;draw();paintControls();}fit();exposition();
 }};
}
