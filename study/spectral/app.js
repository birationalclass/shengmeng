import {filteredSubcomplexExposition} from './filtered-subcomplex.js?v=100';
import {createPageFormation} from './page-formation.js?v=92';
import {createAnimationPlayback} from './animation-playback.js?v=96';
import {createGradedTrace} from './graded-animation.js?v=92';
import {initialTraceContext,selectableTraceOrigin} from './initial-traces.js?v=89';
import {gradedFormulas,createGradedProof} from './associated-graded.js?v=91';
import {createPanelStyle} from './panel-style.js?v=78';
import {renderMathematics} from './math-notation.js?v=77';
import {createStabilityView} from './stability-view.js?v=108';
import {installReadingTouch} from './reading-touch.js?v=74';
import {createAbutmentView} from './abutment-view.js?v=99';
import {createReadingRail} from './reading-rail.js?v=82';
import {fitDiagramSurface} from './diagram-viewport.js?v=67';
import {alignDiagramRelation} from './diagram-labels.js?v=84';
import {numberedPages} from './reading-pages.js?v=103';
import {createReadingFocus} from './reading-focus.js?v=80';
import {replaceBigradedLabel} from './bigraded-labels.js?v=64';
import {visualMotion} from './visual-style.js?v=41';
import {createInitialAnimations} from './initial-animations.js?v=96';
import {createFiltrationTrace} from './filtration-animations.js?v=92';
import {replaceMathContent} from './math-transitions.js?v=97';
import {syncGraphChildren,fadeGraphAddition,restingOpacity} from './diagram-dom.js?v=41';
import {createDegreeSweep,createIndexedSweep,createTotalTrace} from './total-animations.js?v=92';
import {Complex,examples,texVector,matrixTex,q,rank,basisVector} from './algebra.js';
import {lessons,convergence,initial,totalCohomology} from './content.js?v=107';
import {translatePage,language,toggleLanguage} from './language.js?v=77';
import {operationMarkup,viewNames,actionNames,totalDegreeTex} from './workbench.js?v=90';
import {createFilteredView} from './filtered-view.js?v=99';
import {createPageEvolution} from './page-evolution.js?v=106';
import {createNotebookMotion} from './notebook-motion.js?v=92';
import {createSquareTrace} from './element-trace.js?v=57';
const $=s=>document.querySelector(s),raw=String.raw;
const GRID_MAX=4, INITIAL_STEPS=11;
const GRID_ORIGIN={x:170,y:370};
const squareTrace=createSquareTrace($('#diagram'));
const initialAnimations=createInitialAnimations({diagram:$('#diagram')});
const panelStyle=createPanelStyle({language});
const notebookMotion=createNotebookMotion({language});
const readingFocus=createReadingFocus({motion:notebookMotion,column:$('.explanation'),mobilePane:$('.slide-body')});
const revealedReadings=new Map(),foldedReadings=new Set(),foldedSections=new Set();
const openStatements=new Set(),openBuilds=new Set([0]),visitedStatements=new Set();
let revealedBuild=-1,revealedTotalStep=0,revealedFiltrationStep=0,revealedGradedStep=0;
const readingSections=[['initial:0','learn:6'],['learn:5','converge:0','learn:3','learn:4','converge:1','converge:2','converge:3']];
const readingOrder=readingSections.flat();
const readingSection=key=>String(readingSections.findIndex(section=>section.includes(key))+1||2);
const NODE_HALF_W=34,NODE_HALF_H=19;
// Both continuation marks share the same visible edge gap and dot geometry.
const EXTENT={gap:24,radius:1.15,step:6};
const state={module:'initial',cover:true,gradedMode:'space',initialReveal:-1,totalStep:0,filtrationStep:0,notePage:0,annotationStep:1,diagramMode:'3d',stackR:null,stackStart:0,seenH:false,seenV:false,effect:null,pinned:null,pinnedKey:null,step:0,n:3,p:1,r:0,direction:'both',example:'survive',lambda:0,selected:null,totalOrigin:null};
let fitDiagram=()=>{},diagramResizeObserver=null,definitionAnimations=[],expositionContext=null;const complexes=Object.fromEntries(Object.entries(examples).map(([k,x])=>[k,new Complex(x)]));
const traceComplex=new Complex({...examples.d2,gens:[...examples.d2.gens,{id:'x',p:0,q:0},{id:'y',p:0,q:1}],v:[...examples.d2.v,['x','y',1]]});
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const math=(tex,display=false)=>renderMathematics(katex,tex,display);
const gradedProof=createGradedProof({board:$('#operationBoard'),math,language});
const readingRail=createReadingRail({workspace:$('.notebook-workspace'),column:$('.explanation'),mobilePane:$('.slide-body'),content:$('#explanation'),language,cancelFollow:readingFocus.cancel});
// Control labels use the same mathematical typesetting as the diagram.
const mathControlLabel=name=>esc(name).replace(/([EZBd])([₀₁₂₃₄₅₆₇₈₉ᵣ₊]+|\d+)/g,(_,symbol,index)=>math(`${symbol}_{${[...index].map(c=>({'₀':'0','₁':'1','₂':'2','₃':'3','₄':'4','₅':'5','₆':'6','₇':'7','₈':'8','₉':'9','ᵣ':'r','₊':'+'}[c]||c)).join('')}}`));
const evolution=createPageEvolution({origin:GRID_ORIGIN,viewport:$('.diagram-viewport'),diagram:$('#diagram'),controls:$('#diagramControls'),board:$('#operationBoard'),math,language});
const stabilityView=createStabilityView({viewport:$('.diagram-viewport'),board:$('#operationBoard'),controls:$('#diagramControls'),math,language});
const abutmentView=createAbutmentView({viewport:$('.diagram-viewport'),board:$('#operationBoard'),controls:$('#diagramControls'),math,language});
const filteredView=createFilteredView({viewport:$('.diagram-viewport'),diagram:$('#diagram'),point:(p,q)=>xy(p,q),board:$('#operationBoard'),math,language});
const degreeSweep=createDegreeSweep({diagram:$('#diagram'),read:()=>state.n,write:n=>{state.n=n;render(false);if($('#nRange')){$('#nRange').value=n;$('#nRange').nextElementSibling.textContent=n;}},outline:n=>diagonalRegion(xy(0,n),xy(n,0)),line:n=>`M${xy(0,n)} L${xy(n,0)}`});
const pageFormation=createPageFormation({host:$('#diagram'),point:(p,q)=>xy(p,q),math});
const gradedTrace=createGradedTrace({host:$('#diagram'),point:(p,q)=>xy(p,q),read:()=>state});
const totalTrace=createTotalTrace({host:$('#diagram'),point:(p,q)=>xy(p,q),origin:differentialOrigin});
const filtrationSweep=createIndexedSweep({diagram:$('#diagram'),read:()=>state.p,write:p=>{state.p=p;render(false);const input=$('#pRange');if(input){input.value=p;input.nextElementSibling.textContent=p;}},outline:p=>diagonalRegion(xy(p,state.n-p),xy(state.n,0)),line:p=>`M${xy(p,state.n-p)} L${xy(state.n,0)}`,values:()=>Array.from({length:state.n+1},(_,p)=>p),publishName:'spectralFiltrationSweep'});
const filtrationTrace=createFiltrationTrace({host:$('#diagram'),point:(p,q)=>xy(p,q),read:()=>({n:state.n,p:state.p})});
const playback=createAnimationPlayback({language,ready:()=>{
 if(notebookMotion.isAnimating())return false;
 return !$('#explanation').getAnimations({subtree:true}).some(a=>a.playState==='running'&&a.effect?.getComputedTiming().endTime!==Infinity);
},prepareEntrance:()=>{if(isDoubleComplexView()&&state.initialReveal<=2)initialAnimations.prepare(state.initialReveal);},enter:playCurrentEntrance,play:playCurrentAnimation,stop:stopDiagramAnimation,prepare:()=>{if(state.module==='learn'&&state.step===5&&state.notePage===0)pageFormation.prepare(Math.max(1,state.r));},settle:()=>evolution.showResult()});
const block=(t,concept='',number='')=>`<div class="math-block${number?' has-subnumber':''}" data-formula="${esc(t)}" ${concept?`data-concept="${concept}"`:''} role="button" tabindex="0" aria-label="${concept?ui('点击播放对应动画','Click to play this animation'):ui('放大查看公式','Enlarge formula')}">${number?`<span class="formula-subnumber">${number}</span>`:''}${math(t,true)}<button class="formula-zoom" data-zoom aria-label="放大查看公式" title="点击放大公式">↗</button></div>`;
const scene=()=>state.module==='trace'?traceComplex:complexes[state.example];
const pageR=()=>state.module==='trace'&&state.step>=4?state.step-2:state.r;
const stepCount=()=>({initial:initial.length,learn:lessons.length-1,lab:scene().maxP+3,trace:6,converge:convergence.length})[state.module];
let layout={dx:125,dy:75};
const xy=(p,q)=>[GRID_ORIGIN.x+p*layout.dx,GRID_ORIGIN.y-q*layout.dy];
const shifted=(s,k)=>k===0?s:`${s}${k>0?'+':''}${k}`;
function label(x,y,tex,w=116,h=38,small=false,align=''){return `<g class="math-anchor" data-align="${align}" data-x="${x-w/2}" data-y="${y-h/2}" data-width="${w}" data-height="${h}" data-small="${small}" data-tex="${esc(tex)}"><title>${esc(tex)}</title></g>`;}
function line(x1,y1,x2,y2,type,hot,tex=''){let dx=x2-x1,dy=y2-y1,len=Math.hypot(dx,dy),pad=Math.min(dx===0?Infinity:NODE_HALF_W*len/Math.abs(dx),dy===0?Infinity:NODE_HALF_H*len/Math.abs(dy))+5;const f=pad/len;x1+=dx*f;y1+=dy*f;x2-=dx*f;y2-=dy*f;let out=`<path data-concept="${arrowConcept(type)}" tabindex="0" role="button" aria-label="${arrowConcept(type)}" class="arrow ${type} ${hot?'hot':''} " d="M${x1},${y1} L${x2},${y2}" marker-end="url(#arrow-${type})"/>`;if(tex){const compact=['\\delta_1','\\delta_2','d_0','d_1'].includes(tex);out+=label((x1+x2)/2+(dx===0?(compact?23:26):0),(y1+y2)/2+(dy===0?(compact?-14:-17):0),tex,compact?36:68,compact?20:24,true);}return out;}
function svgStart(maxP=GRID_MAX,maxQ=GRID_MAX){
 layout={dx:500/maxP,dy:300/maxQ};
 const [originX,originY]=xy(0,0);
 let out=`<svg viewBox="0 0 840 525" role="img" aria-labelledby="graphTitle"><title id="graphTitle">${esc($('#sceneTitle').textContent)}；横轴第一指标，纵轴第二指标</title><defs>`;
 for(const [id,color] of [['h','var(--teal)'],['v','var(--blue)'],['r','var(--gold)'],['continuation','#8da7ae'],['axis','#78939d']])out+=`<marker id="arrow-${id}" markerUnits="userSpaceOnUse" markerWidth="10" markerHeight="10" viewBox="0 0 10 10" refX="8" refY="5" orient="auto"><path d="M2,1.75 L8,5 L2,8.25" fill="none" stroke="${color}" stroke-width="1.35" stroke-linecap="round" stroke-linejoin="round"/></marker>`;
 // The axes cross at the centre of the (0,0) term. Mask their portions behind
 // terms so even dimmed/zero nodes retain unobstructed mathematical labels.
 out+='<mask id="coordinate-axis-mask" maskUnits="userSpaceOnUse" x="0" y="0" width="840" height="525"><rect width="840" height="525" fill="white"/>';
 const maskTerm=(p,q)=>{const [x,y]=xy(p,q);return `<rect x="${x-NODE_HALF_W-4}" y="${y-NODE_HALF_H-4}" width="${2*NODE_HALF_W+8}" height="${2*NODE_HALF_H+8}" rx="8" fill="black"/>`;};
 for(let p=0;p<=maxP;p++)out+=maskTerm(p,0);
 for(let q=0;q<=maxQ;q++)if(q!==0)out+=maskTerm(0,q);
 out+='</mask><mask id="term-connection-mask" maskUnits="userSpaceOnUse" x="0" y="0" width="840" height="525"><rect width="840" height="525" fill="white"/>';
 for(let p=0;p<=maxP;p++)for(let q=0;q<=maxQ;q++)out+=maskTerm(p,q);
 out+='</mask><linearGradient id="node-glass" x1="0" y1="0" x2="1" y2="1"><stop stop-color="var(--graph-glass-start)" stop-opacity=".19"/><stop offset=".45" stop-color="var(--graph-glass-mid)" stop-opacity=".14"/><stop offset="1" stop-color="var(--graph-glass-end)" stop-opacity=".32"/></linearGradient></defs>';
 for(let p=0;p<=maxP;p++){
  const [x]=xy(p,0);
  if(p!==0)out+=`<path class="grid" d="M${x},38 V${originY+20}"/>`;
  out+=`<text class="axis-text axis-tick" data-axis="p" data-value="${p}" x="${x}" y="${originY+38}" text-anchor="middle">${p}</text>`;
 }
 for(let q=0;q<=maxQ;q++){
  const [,y]=xy(0,q);
  if(q!==0)out+=`<path class="grid" d="M${originX-40},${y} H${originX+570}"/>`;
  if(q!==0)out+=`<text class="axis-text axis-tick" data-axis="q" data-value="${q}" x="${originX-56}" y="${y+5}" text-anchor="end">${q}</text>`;
 }
 out+=`<g class="coordinate-axes" data-origin-x="${originX}" data-origin-y="${originY}" mask="url(#coordinate-axis-mask)"><path id="p-axis" class="coordinate-axis" d="M${originX-45},${originY} H${originX+600}" marker-end="url(#arrow-axis)"/><path id="q-axis" class="coordinate-axis" d="M${originX},${originY+32} V8" marker-end="url(#arrow-axis)"/></g><text class="axis-text axis-name" data-axis-name="p" x="${originX+602}" y="${originY-11}">p</text><text class="axis-text axis-name" data-axis-name="q" x="${originX-17}" y="17">q</text>`;
 return out;
}
function node(p,qv,tex,{dim,muted=false,active=false}={}){let [x,y]=xy(p,qv);return `<g class="node ${muted?'muted':''} ${active?'trace-active':''} ${state.selected?.p===p&&state.selected?.q===qv?'selected':''} ${dim===0?'zero':''}" role="button" tabindex="0" data-p="${p}" data-q="${qv}"${selectableTraceOrigin(state,p,qv)?' data-origin-selectable':''} aria-label="位置 (${p},${qv})${dim!==undefined?`, 维数 ${dim}`:''}"><rect class="node-bg" x="${x-NODE_HALF_W}" y="${y-NODE_HALF_H}" width="${2*NODE_HALF_W}" height="${2*NODE_HALF_H}" rx="9"/><rect class="node-tint" x="${x-NODE_HALF_W}" y="${y-NODE_HALF_H}" width="${2*NODE_HALF_W}" height="${2*NODE_HALF_H}" rx="9" aria-hidden="true"/>${label(x,y,tex,67,36,tex.length>28)}</g>`;}
// Rounded convex hull of the endpoint term boxes, with a four-unit margin.
// This is the smallest convex grouping region with these rounded corner offsets.
function diagonalRegion(start,end){
 const radius=13,a=NODE_HALF_W+4-radius,b=NODE_HALF_H+4-radius;
 const points=[start,end].flatMap(([x,y])=>[[-a,-b],[a,-b],[a,b],[-a,b]].map(([dx,dy])=>[x+dx,y+dy]));
 const unique=[...new Map(points.map(point=>[point.join(','),point])).values()].sort((a,b)=>a[0]-b[0]||a[1]-b[1]);
 const cross=(a,b,c)=>(b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0]);
 const chain=points=>{const out=[];for(const point of points){while(out.length>1&&cross(out.at(-2),out.at(-1),point)<=0)out.pop();out.push(point);}return out;};
 const hull=chain(unique).slice(0,-1).concat(chain([...unique].reverse()).slice(0,-1));
 const normals=hull.map((point,i)=>{const next=hull[(i+1)%hull.length],dx=next[0]-point[0],dy=next[1]-point[1],length=Math.hypot(dx,dy);return [dy/length,-dx/length];});
 const offset=(point,normal)=>point.map((v,i)=>Number((v+radius*normal[i]).toFixed(3))).join(',');
 return hull.map((point,i)=>{
  const before=normals[(i+hull.length-1)%hull.length],after=normals[i];
  return `${i?'L':'M'}${offset(point,before)} A${radius},${radius} 0 0 1 ${offset(point,after)}`;
 }).join(' ')+' Z';
}
function diagonal(n,p,box=true,showLabel=true){
 // A finite display window must not truncate the actual direct-sum range.
 const first=Math.max(0,p),last=n;if(first>last)return '';
 const start=xy(first,n-first),end=xy(last,n-last);
 let out=box?`<path data-concept="filtration" class="diag-box" data-degree="${n}" data-first="${first}" data-last="${last}" d="${diagonalRegion(start,end)}"/>`:'';
 out+=`<path class="diag" mask="url(#term-connection-mask)" d="M${start.join(',')} L${end.join(',')}"/>`;
 if(showLabel)out+=label(700,17,raw`i+j=${n}`,120,24,true);return out;
}
const formulas=(fs,concepts=[],number='',module='',step=0)=>numberedPages(module,step,fs.length).map((page,index)=>{
 const title=Array.isArray(page.title)?esc(ui(...page.title)):page.title?.name?`${esc(ui(...page.title.name))} ${math(page.title.symbol)}`:page.title?math(page.title):'';
 const content=page.indices.map(i=>{
  const formula=block(fs[i-1],concepts[i-1]||'').replace('class="math-block"',`class="math-block reading-formula" data-annotation="${i}"`);
  if(module==='learn'&&step===4&&i===3)return `<div class="reading-hypothesis"><span>${ui('其中','where')}</span>${formula}</div>`;
  if(module==='converge'&&step===3&&i===4)return formula+consequence(raw`E_{r_0}^{p,q}\cong E_\infty^{p,q}`,'page');
  return formula;
 }).join('');
 return `<section class="numbered-entry" data-reading-page="${index}" hidden><div class="build-heading"><h4><span class="statement-subnumber">${page.number}</span><button data-select-reading="${index}">${title}</button></h4><button class="build-toggle" data-toggle-reading="${index}" aria-expanded="false" aria-label="${ui('展开','Expand')}"><span class="fold-glyph" aria-hidden="true"></span></button></div><div class="build-content">${content}</div></section>`;
}).join('');
function statementHeading(meta,key){
 const subject=(meta.showName&&meta.symbol?esc(meta.name)+' ':'')+(meta.symbol?math(meta.symbol):esc(meta.name||''));
 return `<div class="statement-heading" ${meta.continued?'hidden':''}><span class="statement-label">${meta.kind==='§'?'§ ':''}<span class="statement-number">${meta.number}</span></span><span class="statement-separator" aria-hidden="true">·</span><h3 class="statement-title"><button data-select-statement="${key}" title="${esc(meta.name||'')}">${subject}</button></h3><button class="statement-toggle" data-toggle-statement="${key}" aria-expanded="false" aria-label="展开"><span class="fold-glyph" aria-hidden="true"></span></button></div>`;
}
function statementMarkup(item,module,step,grouped=false){
 const meta=statementMeta(module,step),key=`${module}:${step}`,entries=formulas(item.f,meta.concepts,meta.number,module,step);
 if(grouped)return `<section class="formal-statement reading-group" data-statement="${key}" data-step="${step}" hidden><div class="statement-body">${entries}</div></section>`;
 return `<article class="formal-statement notebook-card${meta.continued?' section-continuation':''}" data-statement="${key}" data-step="${step}" hidden>${statementHeading({...meta,name:meta.name||item.title},key)}<div class="statement-body">${meta.intro?`<p class="formal-intro">${meta.intro}</p>`:''}${entries}<div class="slide-supplement"><details><summary>展开数学理由</summary><p>${item.proof||item.text||''}</p></details></div></div></article>`;
}
function sectionTwoMarkup(){
 const heading=statementHeading(statementMeta('learn',5),'2').replace('data-select-statement','data-select-section').replace('data-toggle-statement','data-toggle-section');
 const groups=readingSections[1].map(key=>{const [module,num]=key.split(':'),step=Number(num);return statementMarkup(module==='learn'?lessons[step+1]:convergence[step],module,step,true);}).join('');
 return `<article class="formal-statement notebook-card notebook-section" data-section="2" hidden>${heading}<div class="statement-body section-body">${groups}</div></article>`;
}
function syncStatementCards(){
 syncInitialEntries();for(const key of revealedReadings.keys())syncReadingEntries(key);
 document.querySelectorAll('[data-statement]').forEach(el=>{
  const key=el.dataset.statement,grouped=el.classList.contains('reading-group'),visible=!state.cover&&visitedStatements.has(key),wasVisible=!el.hidden;
  const open=(grouped||openStatements.has(key)||el.classList.contains('section-continuation'))&&!(key==='initial:0'&&state.initialReveal<0);
  el.hidden=!visible;el.inert=!visible;el.dataset.open=String(open);el.classList.toggle('is-active',key===activeStatementKey());
  notebookMotion.setExpanded(el.querySelector(':scope > .statement-body'),open,{immediate:grouped||!visible||!wasVisible});
  if(!grouped&&visible&&!wasVisible&&open)notebookMotion.revealCard(el);
  const toggle=el.querySelector('.statement-toggle');if(toggle){toggle.setAttribute('aria-expanded',String(open));toggle.setAttribute('aria-label',ui(open?'收起':'展开',open?'Collapse':'Expand'));}
 });
 document.querySelectorAll('.notebook-section[data-section]').forEach(section=>{
  const key=section.dataset.section,visible=!state.cover&&[...section.querySelectorAll('[data-statement]')].some(el=>!el.hidden),wasVisible=!section.hidden,open=!foldedSections.has(key);
  section.hidden=!visible;section.inert=!visible;section.dataset.open=String(open);section.dataset.current=String(readingSection(activeStatementKey())===key);
  notebookMotion.setExpanded(section.querySelector(':scope > .section-body'),open,{immediate:!visible||!wasVisible});
  if(visible&&!wasVisible&&open)notebookMotion.revealCard(section);
  const toggle=section.querySelector('[data-toggle-section]');toggle.setAttribute('aria-expanded',String(open));toggle.setAttribute('aria-label',ui(`${open?'收起':'展开'}第${key}节`,`${open?'Collapse':'Expand'} section ${key}`));
 });
}
function activeStatementKey(){return `${state.module}:${['lab','trace'].includes(state.module)?0:state.step}`;}
function companion(item){
 doubleComplexCompanion(initial[0]);
 if(['lab','trace'].includes(state.module)){
  const key=activeStatementKey(),old=$(`[data-statement="${key}"]`),holder=document.createElement('div');holder.innerHTML=statementMarkup(item,state.module,state.step);const card=holder.firstElementChild;card.dataset.statement=key;card.querySelector('[data-toggle-statement]').dataset.toggleStatement=key;card.querySelector('[data-select-statement]').dataset.selectStatement=key;old.replaceWith(card);
 }
 syncStatementCards();$('#sceneNote').textContent=item.note||'';
}
function labCompanion(){let c=scene(),r=state.r;let stable=r>=c.maxP+1;companion({title:stable?`E${r}：已经稳定`:`第 ${r} 页 · ${examples[state.example].name}`,tag:'EXACT RATIONAL COMPUTATION',f:[r===0?raw`E_0^{p,q}:=\operatorname{Gr}_F^pC^{p+q}\cong K^{p,q}`:raw`E_${r}^{p,q}:=\frac{Z_${r}^{p,q}}{Z_{${r-1}}^{p+1,q-1}+B_{${r-1}}^{p,q}}`,raw`d_${r}:E_${r}^{p,q}\to E_${r}^{${shifted('p',r)},${shifted('q',1-r)}}`],text:examples[state.example].description+' 点击任意节点查看代表元、微分矩阵以及本位置的核和像。',note:'用本页的 r 滑块切换谱序列页，从同一总复形的 Zᵣ、Bᵣ 商空间计算。上同调类使用 [a]ᵣ；所列基是计算选择，不是典范分裂。',proof:'计算全部在 ℚ 上进行，分数约分后精确运算。每页检验 dᵣ²=0，下一页维数等于本页核维数减去入射像维数，并独立计算总上同调。'});let summary='<table class="data-table"><tr><th>n</th><th>dim Hⁿ(C)</th><th>Σ dim E∞ᵖⁿ⁻ᵖ</th></tr>';for(let n=0;n<=c.maxN;n++){let H=c.cohomology(n).dim,sum=0;for(let p=0;p<=n;p++)sum+=c.page(c.maxP+2,p,n-p).dim;summary+=`<tr><td>${n}</td><td>${H}</td><td>${sum}</td></tr>`;}$('[data-statement="lab:0"] > .statement-body').insertAdjacentHTML('beforeend',summary+'</table><p class="badge">由总微分独立核对</p>');let data=c.ex.gens.map(g=>block(raw`${g.id}\in K^{${g.p},${g.q}}`)).join(''); for(let kind of ['h','v'])data+=c.ex[kind].map(([a,b,k])=>block(raw`\delta_${kind==='h'?1:2}${a}=${k===1?'':k===-1?'-':k}${b}`)).join(''); $('[data-statement="lab:0"] > .statement-body').insertAdjacentHTML('beforeend',`<details><summary>例子的全部生成元与微分</summary>${data}<p>每个列出的生成元为一个基向量；所有未列出的空间及微分值为零。</p></details>`);}
function traceCompanion(){const L=state.lambda,rep=L===0?'b':`b${L>0?'+':''}${L}y`;let items=[
{title:'选择同一个 E₁ 类的代表元',f:[raw`\delta_2x=y,\quad \delta_2b=0`,raw`a_0:=${rep}`,raw`a_0-b=\delta_2(${L}x)`],text:'加入一个垂直边界不会改变 E₁ 中的类。调节 λ，观察 a₀=b+λy 是不同上链，却代表同一个垂直上同调类。'},
{title:'横向微分产生一个可消去的项',f:[raw`\delta_1a_0=u`,raw`u=-\delta_2c`,raw`d_1[a_0]=[u]=0`],text:'δ₁a₀ 本身不为零，但它是垂直边界，因此在 E₁ 上为零。该类是 d₁-闭的。'},
{title:'加入修正项 a₁=c',f:[raw`a_1:=c\in K^{1,0}`,raw`\delta_1a_0+\delta_2a_1=u-u=0`],text:'修正项 c 向右一列、向下一行，总次数保持为 1。它抵消了 D(a₀) 在第一列中的分量。'},
{title:'总微分只剩右边第二列',f:[raw`a:=a_0+a_1=${rep}+c`,raw`Da=z\in K^{2,0}`],text:'施加的始终是 D=δ₁+δ₂。抵消之后，残余项位于相隔两列的位置，给出了第二微分。'},
{title:'得到非零的 d₂',f:[raw`d_2:E_2^{0,1}\to E_2^{2,0}`,raw`d_2[a_0+c]_2=[z]_2\ne0`],text:'源和靶都是一维空间，d₂ 是同构。这里 [a₀+c]₂ 是总上链代表元在第二页商空间中的类。'},
{title:'第三页：两个类都不再贡献',f:[raw`E_3^{0,1}=E_3^{2,0}=0`,raw`H^*(C,D)=0`],text:'源上的类不是 d₂-闭的；靶上的类是 d₂-边界。它们以不同原因在下一页为零，不能笼统理解为两个点被动画删除。'}];let item=items[state.step];companion({...item,tag:'FOLLOW A REPRESENTATIVE',note:'本模块使用 d₂ 例子，另加 x→y 的垂直可缩复形。改变 λ 只改变代表元，不改变各页或最终答案。',proof:'新增生成元 x∈K⁰⁰、y∈K⁰¹ 满足 δ₂x=y，其余涉及 x、y 的微分为零。因此它们组成一个垂直可缩直和因子，既不改变 E₁ 及后续各页，也不改变总上同调。'});}
function inspect(){if(state.module==='converge'){$('#inspector').innerHTML='';return;}if(state.module==='learn'&&state.step===0){$('#inspector').innerHTML=block(raw`\operatorname{im}(D:C^{n-1}\to C^n)\subseteq\ker(D:C^n\to C^{n+1})`)+block(raw`[a]_H=[a+Db]_H`);return;}if(state.module==='initial'){$('#inspector').innerHTML=block(raw`K^{p,q}\xrightarrow{\delta_1}K^{p+1,q}`)+block(raw`K^{p,q}\xrightarrow{\delta_2}K^{p,q+1}`)+'<p>图中 p、q 是一般指标；虚线延续箭头表示还有未展开的行列，不表示零空间。</p>';return;}const {p,q:qv}=state.selected||{p:['learn','converge'].includes(state.module)?state.p:0,q:['learn','converge'].includes(state.module)?state.n-state.p:1};if(state.module==='learn'){let s=state.step+1,tex=raw`K^{${p},${qv}}`;let text=`第一指标为 ${p}，第二指标为 ${qv}，总次数为 ${p+qv}。`;if(s===3){tex=raw`E_0^{${p},${qv}}\cong K^{${p},${qv}}`;text+=' 同构由取该列分量给出。';}if(s===4){tex=raw`E_1^{${p},${qv}}\cong H^{${qv}}(K^{${p},\bullet},\delta_2)`;text+=' 这里已经对垂直方向求过上同调。';}if(s===5){tex=raw`E_2^{${p},${qv}}`;text+=' '+ui('已经取过 d₁ 上同调。','Cohomology of d₁ has been taken.');}if(s===6){tex=raw`E_r^{${p},${qv}}`;text+=' 微分靶为 (p+r,q−r+1)。';}$('#inspector').innerHTML=block(tex)+`<p>${text}</p>`;return;}
const c=scene();if(state.module==='trace'&&state.step<4){let gs=c.ex.gens.filter(g=>g.p===p&&g.q===qv);$('#inspector').innerHTML=block(raw`K^{${p},${qv}}=\langle ${gs.map(g=>g.id).join(',')||'0'}\rangle`)+`<p>图中节点是该位置的整个空间；方程中的 b、c、x、y、u、z 是选定基向量。</p>`;return;}
let r=pageR(),E=c.page(r,p,qv),tar=c.page(r,p+r,qv-r+1),M=c.differential(r,p,qv),incoming=c.differential(r,p-r,qv+r-1),outRank=rank(M,tar.dim),inRank=rank(incoming,E.dim),name=state.module==='converge'?'\\infty':r;
let html=block(raw`E_{${name}}^{${p},${qv}}\cong\mathbb Q^{${E.dim}}`);if(E.dim)html+=`<p>选定的商空间基（总上链代表元）：</p>`+E.reps.map(v=>block(raw`[${texVector(v,c.basis(E.n))}]_{${name}}`)).join('');html+=`<p>分子维数 ${E.Z.length}；分母维数 ${E.den.length}。商空间维数 ${E.dim}。</p>`;
if(state.module==='lab'||state.module==='trace'){html+=`<p>微分矩阵：列对应上面的源基，行对应靶的商空间基。</p>`+block(raw`[d_${r}]=${matrixTex(M,tar.dim)}`);html+=`<p>靶位置 (${p+r},${qv-r+1})。靶基：</p>`+block(tar.reps.length?tar.reps.map(v=>raw`[${texVector(v,c.basis(tar.n))}]_${r}`).join(',\;'):raw`\varnothing`);html+=`<p>dim ker d${r} = ${E.dim-outRank}<br>dim im（入射 d${r}）= ${inRank}<br>下一页本位置维数 = ${E.dim-outRank-inRank}</p>`;}else if(E.dim){html+=block(raw`\theta([a]_\infty)=[a]_H+F^{${p+1}}H^{${E.n}}`);}$('#inspector').innerHTML=html;}
function controls(){if(state.module==='converge'){$('#controls').innerHTML='';return;}let html='';$('#controls').inert=false;$('#controls').style.visibility='';if(state.module==='initial'&&state.initialReveal>=5&&state.initialReveal<=11||state.module==='learn'&&state.step===0)html+=`<label>示例总次数 n <input id="nRange" type="range" min="0" max="4" value="${state.n}"><output>${state.n}</output></label>`;if(state.module==='converge'||(state.module==='learn'&&(state.step>=1&&state.step<=2||state.step===5))){html+=`<label>示例总次数 n <input id="nRange" type="range" min="0" max="4" value="${state.n}"><output>${state.n}</output></label><label>滤过 p <input id="pRange" type="range" min="0" max="${state.n+1}" value="${state.p}"><output>${state.p}</output></label>`;}if(state.module==='initial'&&state.initialReveal>=8)html+=`<label>滤过 p <input id="pRange" type="range" min="0" max="${state.n+1}" value="${state.p}"><output>${state.p}</output></label>`;if(state.module==='lab'||state.module==='trace'){html+=`<label>例子 <select id="exampleSelect">${Object.entries(examples).map(([k,e])=>`<option value="${k}" ${k===state.example?'selected':''}>${e.name}</option>`).join('')}</select></label>`;}if(state.module==='lab')html+=`<label>页数 r <input id="rRange" type="range" min="0" max="${scene().maxP+2}" value="${state.r}"><output>${state.r}</output></label>`;if(state.module==='trace')html+=`<label>代表元参数 λ <input id="lambdaRange" type="range" min="-2" max="2" value="${state.lambda}"><output>${state.lambda}</output></label>`;if(state.module==='learn'&&state.step===5||state.module==='converge'&&state.step===1)html+=`<label>r <input id="rRange" type="range" min="1" max="${state.module==='converge'?state.n+2:5}" value="${Math.max(1,state.r)}"><output>${Math.max(1,state.r)}</output></label>`;if(isDoubleComplexView()&&state.initialReveal===4)html+=`<button data-total-demo="anticommute">${ui('重播两路相消','Replay cancellation')}</button>`;if(isDoubleComplexView()&&state.initialReveal===5)html+=`<button data-total-demo="total">${ui('演示','Play')} ${math('n=0\\to4')}</button>`;if(isDoubleComplexView()&&state.initialReveal===6)html+=`<button data-total-demo="totalmap">${ui('演示','Play')} ${math('D=\\delta_1+\\delta_2')}</button><button data-total-demo="totalsquare">${ui('演示','Play')} ${math('D^2=0')}</button>`;if(isDoubleComplexView()&&state.initialReveal===8)html+=`<button data-total-demo="filtration">${ui('演示滤过','Play filtration')}</button><button data-total-demo="filteredmap">${math('D(F^pC^n)')} ${ui('分量迁移','Component images')}</button>`;if(isDoubleComplexView()&&state.initialReveal===11)html+=`<button data-graded-view="space" aria-pressed="${state.gradedMode==='space'}">${ui('滤过商','Graded quotient')}</button><button data-graded-view="differential" aria-pressed="${state.gradedMode==='differential'}">${math(raw`\operatorname{Gr}_F D`)}</button>`;$('#controls').innerHTML=html;}
function render(updateControls=true){
 if(!state.cover&&!(state.module==='initial'&&state.initialReveal<0))visitedStatements.add(activeStatementKey());
 if(!state.cover&&state.module==='initial')revealedBuild=Math.max(revealedBuild,state.initialReveal);
 if(state.module==='initial')companion(initial[state.step]);if(state.module==='learn')companion(state.step===0?totalCohomology:lessons[state.step+1]);if(state.module==='lab')labCompanion();if(state.module==='trace')traceCompanion();if(state.module==='converge')companion(convergence[state.step]);
 $('.inspector .mini-label').textContent='点击图中的项，查看其含义';$('.legend').innerHTML='';$('#panelIndex').textContent='';
 renderPersistentDiagram();if(updateControls)controls();inspect();renderWorkspaceState();fitDiagram();translatePage();readingRail.sync();notebookMotion.sync();window.spectralState={...state,language:language()};syncInitialEntrance();syncPlayback();window.spectralFullscreen?.sync();
}
function move(i){state.step=Math.max(0,Math.min(stepCount()-1,i));if(state.module==='lab')state.r=state.step;state.notePage=0;state.annotationStep=1;state.chosenAction=1;state.pinned=null;state.pinnedKey=null;state.selected=null;render();}
function moduleChange(m){activateStatement(`${m}:${m==='learn'?5:0}`);}
$('#beginSlides').onclick=()=>{if(window.spectralBoot?.enter()){state.cover=false;render();}};
$('#coverButton').onclick=()=>{state.module='initial';state.step=0;state.cover=true;state.initialReveal=-1;state.totalStep=0;revealedTotalStep=0;state.filtrationStep=0;revealedFiltrationStep=0;state.gradedMode='space';revealedGradedStep=0;state.notePage=0;state.annotationStep=1;state.totalOrigin=null;notebookMotion.settleAll();state.effect=null;state.chosenAction=1;state.seenH=false;state.seenV=false;state.pinned=null;state.pinnedKey=null;openStatements.clear();visitedStatements.clear();revealedReadings.clear();foldedReadings.clear();foldedSections.clear();revealedBuild=-1;openBuilds.clear();openBuilds.add(0);location.hash='title';render();};
$('#viewTabs').onclick=e=>{const b=e.target.closest('[data-view]');if(b)move(Number(b.dataset.view));};
$('#actionTabs').onclick=e=>{const b=e.target.closest('[data-action]');if(b){state.pinned=null;state.pinnedKey=null;const annotation=Number(b.dataset.action),page=currentReadingPages().findIndex(p=>p.actions.includes(annotation));if(page>=0)selectReadingPage(page);setAnnotation(annotation);applyConcept(null);}};
$('#controls').addEventListener('input',e=>{let id=e.target.id;if(!id.endsWith('Range'))return;if(id==='nRange'){degreeSweep.stop();totalTrace.clear();}if(id==='nRange'||id==='pRange'){filtrationSweep.stop();filtrationTrace.clear();}const val=Number(e.target.value);if(id==='nRange'){state.n=val;if(state.module==='converge')state.r=Math.min(state.r,val+2);state.p=Math.min(state.p,val+1);if($('#pRange')){$('#pRange').max=val+1;$('#pRange').value=state.p;$('#pRange').nextElementSibling.textContent=state.p;}}if(id==='pRange')state.p=val;if(id==='lambdaRange')state.lambda=val;if(id==='rRange'){state.r=val;if(state.module==='lab')state.step=val;}e.target.nextElementSibling.textContent=val;state.selected=null;render(id==='nRange'&&state.module==='converge');});
$('#controls').onchange=e=>{if(e.target.id==='exampleSelect'){state.example=e.target.value;state.r=0;state.step=0;state.selected=null;render();}};
$('#controls').onclick=e=>{const demo=e.target.closest('[data-total-demo]');if(demo){state.pinned=null;state.pinnedKey=null;applyConcept(demo.dataset.totalDemo);playback.restart(true);return;}let b=e.target.closest('[data-direction]');if(b){state.direction=b.dataset.direction;render();}};
function selectNode(e){
 const b=e.target.closest('[data-p]:not([data-boundary])');if(!b)return;
 const origin={p:Number(b.dataset.p),q:Number(b.dataset.q)};
 if(isDoubleComplexView()){
  if(!selectableTraceOrigin(state,origin.p,origin.q))return;
  const context=initialTraceContext(state),effect=state.initialReveal===6?(state.effect==='totalsquare'?'totalsquare':'totalmap'):context.effect;
  state.totalOrigin=origin;state.selected=origin;if(state.initialReveal===6)state.n=origin.p+origin.q;
  state.effect=effect;state.pinned=effect;state.pinnedKey=null;
  render(false);playback.restart(true,'demonstration');return;
 }
 state.selected=origin;render(false);if(['lab','trace'].includes(state.module))$('.inspector').open=true;
}$('#diagram').onclick=selectNode;$('#diagram').onkeydown=e=>{if(e.key===' '){e.preventDefault();const el=interactiveConcept(e.target);if(el)pinConcept(el.dataset.concept,el);selectNode(e);}};
$('#proofJump').onclick=()=>{moduleChange('converge');$('.workspace').scrollIntoView({behavior:'smooth'});};
// These keys belong only to the left reading sequence, even over right-side controls.
const readingKeys=new Set(['Enter','ArrowRight','ArrowLeft']);
document.addEventListener('keydown',e=>{
 if(e.key==='Tab')readingHoverPaused=false;
 if(!readingKeys.has(e.key))return;
 e.preventDefault();e.stopImmediatePropagation();
 if(e.repeat||e.isComposing)return;
 if(state.cover&&e.key!=='Enter')return;
 navigateReading(e.key==='ArrowLeft'?-1:1);
},true);
document.addEventListener('keyup',e=>{if(readingKeys.has(e.key)){e.preventDefault();e.stopImmediatePropagation();}},true);
// Touch and keyboard share the exact same left-reading navigation boundary.
function navigateReading(direction){
 if(window.spectralMobileReading?.active()){window.spectralMobileReading.navigate(direction);return;}
 if(document.querySelector('dialog[open]'))return;
 if(state.cover){if(direction>0&&!$('#beginSlides').hidden)$('#beginSlides').click();return;}
 if(direction<0)retreatNote();else advanceNote();
}
window.spectralNavigateReading=navigateReading;
installReadingTouch({navigate:navigateReading});
window.addEventListener('hashchange',()=>{let m=location.hash.slice(1);if(state.cover){if(m!=='title')history.replaceState(null,'',location.pathname+location.search+'#title');return;}if(m==='title'&&!state.cover){$('#coverButton').click();return;}if(['initial','learn','lab','trace','converge'].includes(m)&&(m!==state.module||state.cover))moduleChange(m);});
document.querySelectorAll('[data-tex]').forEach(el=>el.innerHTML=math(el.dataset.tex));
// Every fresh visit waits on the title slide, including saved lesson URLs.
history.replaceState(null,'',location.pathname+location.search+'#title');
$('#languageButton').onclick=$('#coverLanguage').onclick=()=>{toggleLanguage();render();if(!state.cover)keepReadingVisible($('.build-current')||$('[data-build="0"]'));};
$('#coverLanguage').disabled=false;
render();

function openFormula(e){const el=e.target.closest('[data-formula]');if(!el||el.closest('#formulaDialog')||(el.dataset.concept&&!e.target.closest('[data-zoom]')))return;$('#formulaContent').innerHTML=math(el.dataset.formula,true);$('#formulaDialog').showModal();}
document.addEventListener('click',openFormula);
document.addEventListener('keydown',e=>{if((e.key===' ')&&e.target.matches('[data-formula]')){e.preventDefault();if(e.target.dataset.concept){revealAnnotation(e.target);pinConcept(e.target.dataset.concept,interactiveConcept(e.target));}else openFormula(e);}});
$('#closeFormula').onclick=()=>$('#formulaDialog').close();

function statementMeta(module=state.module,step=state.step){
 if(module==='learn'&&step===6)return {kind:'§',number:'1',continued:true,concepts:['cycles','boundaries']};
 const collections={
 initial:[
 {kind:'定义',number:'1.1',name:'双复形',symbol:raw`(K,\delta_1,\delta_2)`,intro:'在上述双分次向量空间上给定以下线性映射，并要求它们满足所列恒等式。',concepts:['delta1','delta2','differential','differential']},
 {kind:'定义',number:'1.2',name:'总复形',symbol:raw`(C^\bullet,D)`,intro:'对每个总次数 n，将同一条对角线上的空间取直和，并定义总微分。',concepts:['total','differential','differential']}
 ],
 learn:[
 {kind:'定义',number:'2.1',name:'上同调',symbol:raw`H^n(C^\bullet,D)`,concepts:['cycles','boundaries','cohomology','cohomology']},
 {kind:'定义',number:'2.2',name:'列滤过',symbol:raw`F^\bullet C^\bullet`,concepts:['filtration','filtration','differential']},
 {kind:'定义',number:'2.3',name:'关联分次与第零页',symbol:raw`(E_0,d_0)`,concepts:['quotient','quotient','space']},
 {kind:'§',number:'2',name:'E₀',symbol:raw`(E_0,d_0)`,concepts:['quotient','delta2']},
 {kind:'定义',number:'2.1',name:'E₁',symbol:raw`(E_1,d_1)`,concepts:['cohomology','delta1','delta1']},
 {kind:'定义',number:'2.3',name:'滤过闭链、边界与一般页',symbol:raw`(E_r,d_r)`,concepts:['cycles','boundaries','page','differential']}
 ],
 converge:[
 {name:'稳定项',concepts:['page','page']},
 {name:'逐位置稳定',concepts:['page','differential','page']}
 ]};
 const meta=collections[module]?.[step]||{kind:module==='lab'?'例':'计算',concepts:module==='lab'?['page','differential']:['differential','space','differential']};
 const order=readingOrder.indexOf(`${module}:${['lab','trace'].includes(module)?0:step}`);
 if(module==='initial'&&step===0)return {...meta,kind:'§',number:'1',name:ui('双复形','Double complex'),symbol:null};
 if(module==='learn'&&step>=3&&step<=6)return {...meta,kind:'§',number:'2',name:ui('谱序列','Spectral sequence'),symbol:raw`(E_r,d_r)`,showName:true,continued:step!==5};
 if(['converge','lab','trace'].includes(module))return {...meta,kind:'§',number:'2',continued:true};
 return {...meta,number:order<0?meta.number:String(order+1)};
}
function arrowConcept(type){return type==='h'?'delta1':type==='v'?'delta2':'differential';}
function renderWorkspaceState(){
 const diagram=$('#diagram'),canSelect=!!initialTraceContext(state);
 diagram.classList.toggle('origin-selection',canSelect);
 const deck=$('.slide-deck'),cover=state.cover;deck.dataset.module=state.module;$('.visualization-module').classList.toggle('general-page-mode',state.module==='learn'&&state.step===5||isTransitionReading());
 document.body.classList.toggle('at-cover',cover);
 deck.classList.toggle('is-building',isDoubleComplexView());deck.classList.toggle('is-coordinate-intro',isDoubleComplexView()&&state.initialReveal<0);deck.classList.toggle('is-cover',cover);deck.classList.toggle('has-diagram',!cover);deck.classList.toggle('has-explanation',!cover);
 if(cover)window.spectralBoot?.showCover();$('.slide-body').inert=cover;$('#visualPanel').inert=cover;
 $('#sceneTitle').textContent=ui('谱序列','Spectral Sequence');
 $('#viewTabs').innerHTML=['lab','trace'].includes(state.module)?viewNames(state,language()).map((t,i)=>`<button data-view="${i}" aria-pressed="${state.step===i}">${mathControlLabel(t)}</button>`).join(''):'';
 $('#sceneNote').hidden=true;renderQuickCheck();
 if(isDoubleComplexView())setupDoubleComplex();else updateAnnotations();syncStatementCards();applyConcept(state.pinned,false);
}
function ui(zh,en){return language()==='en'?en:zh;}
function selectInitialBuild(index,substep=0){
 foldedSections.delete('1');
 if(!(isDoubleComplexView()&&state.initialReveal===index)){state.totalOrigin=null;state.selected=null;if(index===6)state.n=2;if(index===11){state.n=2;state.p=1;}}
 if(index===8&&substep===1)state.p=Math.min(1,state.n);
 state.filtrationStep=index===8?substep:0;if(index===8)revealedFiltrationStep=Math.max(revealedFiltrationStep,substep);
 state.totalStep=index===6?substep:0;if(index===6)revealedTotalStep=Math.max(revealedTotalStep,substep);
 if(index===11){state.gradedMode=substep===1?'differential':'space';revealedGradedStep=Math.max(revealedGradedStep,substep);}
 state.cover=false;state.module='initial';state.step=0;state.initialReveal=index;openStatements.add('initial:0');openBuilds.add(index);state.seenH=index>=1;state.seenV=index>=2;state.effect=initialConcept();state.pinned=null;state.pinnedKey=null;render();
 keepDefinitionVisible();

}
function activateStatement(key,last=false){
 const [module,number]=key.split(':'),step=Number(number);if(key===activeStatementKey()&&openStatements.has(key))return;
 foldedSections.delete(readingSection(key));
 state.cover=false;state.module=module;state.step=step;state.notePage=0;state.annotationStep=1;state.chosenAction=1;state.pinned=null;state.pinnedKey=null;state.stackR=null;state.effect=null;state.selected=null;state.totalOrigin=null;
 openStatements.add(key);
 if(module==='initial')selectInitialBuild(last?INITIAL_STEPS:Math.max(0,state.initialReveal),last?1:0);
 else{
  if(module==='learn'&&step===6){state.n=2;state.p=1;state.r=2;}else if(module==='learn'&&step===5)state.r=Math.max(1,state.r);else if(module==='lab')state.r=0;
  const pages=currentReadingPages();state.notePage=last?pages.length-1:0;foldedReadings.delete(`${key}:${state.notePage}`);state.annotationStep=state.chosenAction=pages[state.notePage]?.focus||1;
  render();keepReadingVisible($(`[data-statement="${key}"] [data-reading-page="${state.notePage}"]`));
 }
 history.replaceState(null,'',location.pathname+location.search+'#'+key.replace(':','-'));
}
function currentReadingPages(){return numberedPages(state.module,state.step,annotationCount());}
function selectReadingPage(index){foldedSections.delete(readingSection(activeStatementKey()));const pages=currentReadingPages();state.notePage=Math.max(0,Math.min(index,pages.length-1));foldedReadings.delete(`${activeStatementKey()}:${state.notePage}`);openStatements.add(activeStatementKey());state.annotationStep=state.chosenAction=pages[state.notePage].focus;state.pinned=null;state.pinnedKey=null;state.stackR=null;render();keepReadingVisible($(`[data-statement="${activeStatementKey()}"] [data-reading-page="${state.notePage}"]`));}
// Auto-folding is a reading-navigation preference, never a hover or proof effect.
// Changing the setting leaves the current layout untouched until the next advance.
function foldBeforeAdvance(nextStatement){
 if(!notebookMotion.autoCollapse())return;
 for(const key of openStatements)if(key!==nextStatement)openStatements.delete(key);
 openBuilds.clear();
 for(const [key,last] of revealedReadings)for(let i=0;i<=last;i++)foldedReadings.add(`${key}:${i}`);
}
function advanceNote(){
 if(isDoubleComplexView()&&state.initialReveal===8&&state.filtrationStep===0){selectInitialBuild(8,1);return;}
 if(isDoubleComplexView()&&state.initialReveal===11&&state.gradedMode==='space'){selectInitialBuild(11,1);return;}
 if(isDoubleComplexView()&&state.initialReveal===6&&state.totalStep===0){selectInitialBuild(6,1);return;}
 if(isDoubleComplexView()&&state.initialReveal<INITIAL_STEPS){foldBeforeAdvance('initial:0');selectInitialBuild(state.initialReveal+1);return;}
 if(!isDoubleComplexView()&&state.notePage<currentReadingPages().length-1){foldBeforeAdvance(activeStatementKey());selectReadingPage(state.notePage+1);return;}
 const i=readingOrder.indexOf(activeStatementKey());
 if(i>=0&&i<readingOrder.length-1){const next=readingOrder[i+1];foldBeforeAdvance(next);activateStatement(next);}
}
function retreatNote(){if(isDoubleComplexView()){if(state.initialReveal===8&&state.filtrationStep===1){selectInitialBuild(8,0);return;}if(state.initialReveal===11&&state.gradedMode==='differential'){selectInitialBuild(11,0);return;}if(state.initialReveal===6&&state.totalStep===1){selectInitialBuild(6,0);return;}if(state.initialReveal>0){selectInitialBuild(state.initialReveal-1,[7,9].includes(state.initialReveal)?1:0);}return;}if(state.notePage>0){selectReadingPage(state.notePage-1);return;}const i=readingOrder.indexOf(activeStatementKey());if(i>0){activateStatement(readingOrder[i-1],true);}}
$('#explanation').addEventListener('click',e=>{
 const sectionToggle=e.target.closest('[data-toggle-section]'),sectionSelect=e.target.closest('[data-select-section]');
 if(sectionToggle){
  notebookMotion.settleAll();const key=sectionToggle.dataset.toggleSection;
  if(foldedSections.has(key))foldedSections.delete(key);else foldedSections.add(key);
  syncStatementCards();return;
 }
 if(sectionSelect){const section=sectionSelect.dataset.selectSection;foldedSections.delete(section);activateStatement(readingSections[Number(section)-1][0]);syncStatementCards();return;}
 const toggle=e.target.closest('[data-toggle-statement]'),select=e.target.closest('[data-select-statement]'),buildToggle=e.target.closest('[data-toggle-build]'),buildSelect=e.target.closest('[data-select-build]'),readingToggle=e.target.closest('[data-toggle-reading]'),readingSelect=e.target.closest('[data-select-reading]');
 if(toggle){notebookMotion.settleAll();const key=toggle.dataset.toggleStatement;if(toggle.getAttribute('aria-expanded')==='true'){openStatements.delete(key);syncStatementCards();}else activateStatement(key);return;}
 if(select){activateStatement(select.dataset.selectStatement);return;}
 if(buildToggle){const i=Number(buildToggle.dataset.toggleBuild);if(openBuilds.has(i)){openBuilds.delete(i);syncInitialEntries();}else selectInitialBuild(i);return;}
 if(buildSelect){const i=Number(buildSelect.dataset.selectBuild),current=isDoubleComplexView()&&state.initialReveal===i;selectInitialBuild(i,current?(i===6?state.totalStep:i===8?state.filtrationStep:i===11&&state.gradedMode==='differential'?1:0):0);return;}
 if(readingToggle||readingSelect){
  const button=readingToggle||readingSelect,index=Number(button.dataset.toggleReading??button.dataset.selectReading),parent=button.closest('[data-statement]').dataset.statement;
  if(readingToggle&&readingToggle.getAttribute('aria-expanded')==='true'){foldedReadings.add(`${parent}:${index}`);syncReadingEntries(parent);}
  else{if(parent!==activeStatementKey())activateStatement(parent);selectReadingPage(index);}
  return;
 }
 // The whole numbered entry selects its reading position. Explicit controls
 // retain their own action, and formula clicks can still preview the concept.
 const entry=e.target.closest('.build-card,.numbered-entry');
 if(!entry||e.target.closest('button,a,input,select,textarea,summary,[data-zoom]'))return;
 if(entry.matches('.build-card')){
  const index=Number(entry.dataset.build);
  if(!entry.classList.contains('build-current')||!openBuilds.has(index))selectInitialBuild(index);
 }else{
  const parent=entry.closest('[data-statement]').dataset.statement,index=Number(entry.dataset.readingPage);
  if(parent!==activeStatementKey())activateStatement(parent);
  if(!entry.classList.contains('build-current')||foldedReadings.has(`${parent}:${index}`))selectReadingPage(index);
 }
 if(!e.target.closest('.math-block,.relation-choice'))e.stopPropagation();
});
function differentialOrigin(effect=state.effect){const context=initialTraceContext(state);return context&&(context.effect===effect||state.initialReveal===6&&['totalmap','totalsquare'].includes(effect))?context.origin:{p:1,q:1};}
function initialConcept(){return ['space','delta1','delta2','square','anticommute','total',state.totalStep===1?'totalsquare':'totalmap','totalcohom',state.filtrationStep===1?'filteredmap':'filtration','subcomplex','inclusion',state.gradedMode==='differential'?'gradedmap':'graded'][state.initialReveal];}
function keepReadingVisible(card){readingFocus.follow(card);}
function keepDefinitionVisible(){keepReadingVisible($(`[data-build="${state.initialReveal}"]`));}
function interactiveConcept(target){
 if(!(target instanceof Element))return null;
 // A term has local hover/focus feedback; it never selects a diagram-wide concept.
 if(target.closest('#diagram .node'))return null;
 if(target.closest('[data-zoom],.statement-heading,.statement-title,.build-heading'))return null;
 const choice=target.closest('.relation-choice');if(choice)return choice;
 const build=target.closest('.build-statement.is-active .build-card[data-open="true"]');
 // Each total-complex formula is its own trigger for the same degree sweep.
 // Clicking C^bullet or C^n selects that formula without a hover side effect.
 if(build)return (build.querySelector('.relation-choices')||['total','totalmap','filtration','graded'].includes(build.dataset.concept))?target.closest('.math-block[data-concept]'):build;
 return target.closest('.formal-statement .reading-formula[data-concept]')||target.closest('#diagram [data-concept]');
}
function interactionKey(el){
 if(!el)return null;
 if(el.matches('.relation-choice'))return `relation:${el.dataset.concept}`;
 if(el.closest('.build-card'))return `build:${el.closest('.build-card').dataset.build}`;
 if(el.matches('.formal-statement .reading-formula'))return `formula:${Number(el.dataset.annotation)-1}`;
 return `diagram:${el.dataset.concept}`;
}
function applyConcept(concept,hover=false,source=null){
 if(isDoubleComplexView()&&!concept)concept=initialConcept();
 if(isDoubleComplexView()&&['totalmap','totalsquare'].includes(concept)){const {p,q}=differentialOrigin();state.n=p+q;}
 const key=source?interactionKey(source):state.pinnedKey||(isDoubleComplexView()&&state.initialReveal?`build:${state.initialReveal}`:null);
 if(isDoubleComplexView()&&state.effect!==concept){state.effect=concept;renderPersistentDiagram();}
 const graph=$('#diagram');
 graph.querySelectorAll('.concept-active').forEach(el=>el.classList.remove('concept-active'));
 graph.classList.toggle('concept-focus',!!concept);graph.classList.toggle('hover-effect',!!concept&&hover);
 const targets={square1:'.relation-route',square2:'.relation-route',anticommute:'.relation-route',delta1:'.arrow.h,.continuation[data-concept=delta1]',delta2:'.arrow.v,.continuation[data-concept=delta2]',differential:'.arrow,.continuation[data-concept=delta1],.continuation[data-concept=delta2],.continuation[data-concept=differential]',space:'.node:not(.outside-quadrant) .node-bg',page:'.node:not(.outside-quadrant) .node-bg',quotient:'.node:not(.muted):not(.outside-quadrant) .node-bg',totalsquare:'.relation-route',totalmap:'.diag-box,.diag,#diagram-edges>g:not(.context-edge) .arrow,#diagram-edges>g:not(.context-edge) .continuation',total:'.diag-box,.diag,.node:not(.muted):not(.outside-quadrant) .node-bg,.continuation[data-concept=total]',graded:'.node:not(.muted) .node-bg,.denominator-region',gradedmap:'.node:not(.muted) .node-bg,.arrow.v,.arrow.h',zeropage:'.node:not(.muted):not(.outside-quadrant) .node-bg',filtration:'.diag-box,.node:not(.muted):not(.outside-quadrant) .node-bg',filteredmap:'.diag-box,.diag,#diagram-edges>g:not(.context-edge) .arrow',cycles:'[data-concept=cycles]',boundaries:'[data-concept=boundaries]',cohomology:'.node:not(.muted):not(.outside-quadrant) .node-bg',comparison:'.node:not(.zero) .node-bg,.diag-box'};
 if(concept){
  const selector=targets[concept];
  if(selector)graph.querySelectorAll(selector).forEach(el=>el.classList.add('concept-active'));
 }
 graph.querySelectorAll('.map-label').forEach(el=>el.classList.toggle('map-active',!concept||el.dataset.mapConcept===concept||['totalmap','differential'].includes(concept)||concept==='gradedmap'&&['delta1','delta2'].includes(el.dataset.mapConcept)));
 // Left-hand emphasis belongs to one source item, never to a concept family.
 document.querySelectorAll('.formal-statement .concept-linked').forEach(el=>el.classList.remove('concept-linked'));
 document.querySelectorAll('.formal-statement [aria-pressed]').forEach(el=>el.setAttribute('aria-pressed','false'));
 document.querySelectorAll('.formal-statement.is-active .build-card,.formal-statement.is-active .reading-formula').forEach(el=>{
  const ownKey=interactionKey(el);el.classList.toggle('concept-linked',!!concept&&(ownKey===key||['3','6'].includes(el.dataset.build)&&key?.startsWith('relation:')));
  el.setAttribute('aria-pressed',String(!!state.pinned&&ownKey===state.pinnedKey));
 });
 renderOperation();window.spectralState={...state,language:language()};
}
function pinConcept(concept,source=null){

 const key=interactionKey(source);const same=state.pinned===concept&&state.pinnedKey===key;
 state.pinned=same?null:concept;state.pinnedKey=same?null:key;
 applyConcept(state.pinned,false);playback.restart(true);translatePage();window.spectralState={...state,language:language()};
}
const squareCentres=concept=>concept==='square1'?[xy(1,1),xy(2,1),xy(3,1)]:[xy(1,1),xy(1,2),xy(1,3)];
// Only a click selects an interactive formula; hover/focus are passive.
document.addEventListener('click',e=>{const el=interactiveConcept(e.target);if(el){revealDirections(el);revealAnnotation(el);pinConcept(el.dataset.concept,el);}});

function renderQuickCheck(){
 const checks={initial:['如果先作用 δ₂，再作用 δ₁，终点在哪里？','终点是 Kᵖ⁺¹ᑫ⁺¹。交换作用顺序仍到同一位置，但两条复合映射之和为零。'],learn:['dᵣ 的靶在哪里？总次数改变多少？','靶是 Eᵣᵖ⁺ʳ,ᑫ⁻ʳ⁺¹，因此总次数从 p+q 变成 p+q+1。'],converge:['稳定页是否给出了 Hⁿ 的典范直和分解？','没有。它典范地给出滤过商 GrᵖHⁿ。向量空间层面的分裂可以选择，但收敛本身不指定典范分裂。']};
 const entry=state.module==='initial'?null:checks[state.module],el=$('#quickCheck');el.hidden=!entry||state.cover||state.step!==stepCount()-1;
 el.innerHTML=entry?`<summary><span>自检</span> · <span>${entry[0]}</span></summary><p>${entry[1]}</p>`:'';
}

function continuation(x1,y1,x2,y2,concept=''){const marker=concept==='delta1'?'h':concept==='delta2'?'v':concept==='total'||concept==='differential'?'r':'continuation';return `<path class="continuation" ${concept?`data-concept="${concept}" tabindex="0"`:''} d="M${x1},${y1} L${x2},${y2}" marker-end="url(#arrow-${marker})" role="${concept?'button':'img'}" aria-label="延续箭头：省略中间项，不表示一次微分"><title>延续箭头：省略中间项，不表示一次微分</title></path>`;}

function isDoubleComplexView(){return !state.cover&&state.module==='initial'&&state.step===0;}
function consequence(formula,concept,attribute=''){
 return `<div class="reading-consequence" ${attribute}><span class="consequence-cue">${ui('有','We have')}</span>${block(formula,concept)}</div>`;
}
function doubleComplexCompanion(item){
 $('#sceneTitle').textContent=ui('谱序列','Spectral Sequence');
 if($('.build-statement')?.dataset.contentLanguage===language())return;
 const cards=[
 {title:'横向微分 δ₁',concept:'delta1',f:[item.f[0]]},
 {title:'纵向微分 δ₂',concept:'delta2',f:[item.f[1]]},
 {title:'平方零关系',concept:'square',f:[]},
 {title:'反交换关系',concept:'anticommute',f:[item.f[3]]},
 {title:ui('总对象','Total object'),concept:'total',f:[raw`C^n:=\operatorname{Tot}^nK=\bigoplus_{p+q=n}K^{p,q}`]},
 {title:'总微分',concept:'totalmap',f:[raw`D:=\delta_1+\delta_2:C^n\longrightarrow C^{n+1}`]},
 {title:ui('总上同调','Total cohomology'),concept:'totalcohom',f:[raw`\begin{gathered}H^n(C^\bullet,D):=\\\frac{\ker(D:C^n\to C^{n+1})}{\operatorname{im}(D:C^{n-1}\to C^n)}\end{gathered}`]},
 {title:'列滤过',concept:'filtration',f:[raw`F^pC^n:=\bigoplus_{i\ge p}K^{i,n-i}`,raw`D(F^pC^n)\subseteq F^pC^{n+1}`]},
 {title:ui('滤过子复形','Filtration subcomplex'),concept:'subcomplex',f:[raw`(F^pC^\bullet,D|_{F^pC^\bullet})`,raw`D|_{F^pC^n}:F^pC^n\longrightarrow F^pC^{n+1}`]},
 {title:ui('包含诱导映射','Inclusion-induced map'),concept:'inclusion',f:[raw`\iota_p:(F^pC^\bullet,D)\hookrightarrow(C^\bullet,D)`,raw`\begin{gathered}H^n(\iota_p):\\H^n(F^pC^\bullet,D)\longrightarrow H^n(C^\bullet,D)\end{gathered}`]},
 {title:ui('关联分次函子','Graded functor'),concept:'graded',f:gradedFormulas},
 ];
 const assumptions=[raw`K:=\{K^{p,q}\}_{(p,q)\in\mathbb Z^2}`];
 $('#explanation').dataset.notebook=language();
 const heading=statementHeading(statementMeta('initial',0),'1').replace('data-select-statement','data-select-section').replace('data-toggle-statement','data-toggle-section');
 $('#explanation').innerHTML=`<article class="formal-statement notebook-card notebook-section" data-section="1" hidden>${heading}<div class="statement-body section-body"><section class="formal-statement build-statement reading-group is-active" data-statement="initial:0" data-step="0" hidden data-content-language="${language()}"><div class="statement-body"><section class="build-card" data-build="0" data-concept="space" hidden><div class="build-heading"><h4><span class="statement-subnumber">1.1</span><button data-select-build="0">${ui('对象','Object')} ${math(raw`K^{-,-}`)}</button></h4><button class="build-toggle" data-toggle-build="0" aria-expanded="false" aria-label="展开"><span class="fold-glyph" aria-hidden="true"></span></button></div><div class="build-content">${assumptions.map(f=>block(f,'space')).join('')}</div></section>${cards.map((c,i)=>`<section class="build-card" data-build="${i+1}" data-concept="${c.concept}" hidden><div class="build-heading"><h4><span class="statement-subnumber">1.${i+2}</span><button data-select-build="${i+1}">${c.title}</button></h4><button class="build-toggle" data-toggle-build="${i+1}" aria-expanded="false" aria-label="展开"><span class="fold-glyph" aria-hidden="true"></span></button></div><div class="build-content">${c.f.map((f,j)=>c.concept==='filtration'&&j===1?consequence(f,'filteredmap','data-filtration-fragment hidden'):c.concept==='graded'&&j===1?`<div data-graded-fragment hidden>${block(f,'gradedmap')}</div>`:block(f,c.concept==='filtration'&&j===1?'filteredmap':c.concept)).join('')}${i===2?`<div class="relation-choices"><button class="relation-choice" data-concept="square1">${math(raw`\delta_1^2=0`)}</button><button class="relation-choice" data-concept="square2">${math(raw`\delta_2^2=0`)}</button></div>`:i===5?consequence(raw`D^2=0`,'totalsquare','data-total-fragment hidden'):''}</div></section>`).join('')}</div></section>${statementMarkup(lessons[7],'learn',6,true)}</div></article>`;
 $('#explanation').insertAdjacentHTML('beforeend',sectionTwoMarkup());
 $('#sceneNote').textContent='';
}
// Folding stays manual unless the reader explicitly enables auto-collapse.
// Navigation records that choice before these shared accordion views synchronize.
function syncNumberedEntry(el,visible,open,current){
 const wasVisible=!el.hidden,body=el.querySelector(':scope > .build-content');
 el.hidden=!visible;el.inert=!visible;el.dataset.open=String(open);
 el.classList.toggle('build-current',current);el.classList.add('is-available');
 notebookMotion.setExpanded(body,open,{immediate:!visible||!wasVisible});
 if(visible&&!wasVisible&&open)notebookMotion.revealCard(el);
 const toggle=el.querySelector('.build-toggle');
 toggle.setAttribute('aria-expanded',String(open));toggle.setAttribute('aria-label',ui(open?'收起':'展开',open?'Collapse':'Expand'));
}
function syncInitialEntries(){
 document.querySelectorAll('.build-statement .build-card').forEach(el=>{
  const i=Number(el.dataset.build);syncNumberedEntry(el,i<=revealedBuild,openBuilds.has(i),isDoubleComplexView()&&i===state.initialReveal);
  el.classList.toggle('build-complete',i<state.initialReveal);
  if(i===11){
   el.dataset.gradedMode=state.gradedMode;
   const fragment=el.querySelector('[data-graded-fragment]');
   fragment.dataset.current=String(isDoubleComplexView()&&state.initialReveal===11&&state.gradedMode==='differential');
   notebookMotion.setExpanded(fragment,revealedGradedStep===1,{immediate:state.cover||el.hidden});
  }
  if(i===8){
   el.dataset.filtrationStep=String(state.filtrationStep);
   const fragment=el.querySelector('[data-filtration-fragment]');
   fragment.dataset.current=String(isDoubleComplexView()&&state.initialReveal===8&&state.filtrationStep===1);
   notebookMotion.setExpanded(fragment,revealedFiltrationStep===1,{immediate:state.cover||el.hidden});
  }
  if(i===6){
   el.dataset.totalStep=String(state.totalStep);
   const fragment=el.querySelector('[data-total-fragment]');
   // A revealed formula stays in the notebook; only its reading emphasis changes.
   const shown=revealedTotalStep===1;
   fragment.dataset.current=String(isDoubleComplexView()&&state.initialReveal===6&&state.totalStep===1);
   notebookMotion.setExpanded(fragment,shown,{immediate:state.cover||el.hidden});
  }
 });
}
function syncReadingEntries(key){
 const last=revealedReadings.get(key)??-1;
 document.querySelectorAll(`[data-statement="${key}"] [data-reading-page]`).forEach(el=>{
  const i=Number(el.dataset.readingPage),visible=i<=last,current=key===activeStatementKey()&&i===state.notePage;
  syncNumberedEntry(el,visible,visible&&!foldedReadings.has(`${key}:${i}`),current);
 });
}
function setupDoubleComplex(){
 $('.build-statement').classList.remove('is-coordinate-prelude');$('.build-statement').inert=false;$('.build-statement').removeAttribute('aria-hidden');
 $('#actionTabs').innerHTML='';$('#sceneNote').textContent='';$('#sceneNote').hidden=true;
 $('#controls').inert=state.initialReveal<4;$('#controls').style.visibility=state.initialReveal<4?'hidden':'visible';syncStatementCards();
}
function revealDirections(el){
 if(!isDoubleComplexView())return;
 const concept=el.dataset.concept;
 if(['delta1','square1','anticommute','totalmap'].includes(concept))state.seenH=true;
 if(['delta2','square2','anticommute','totalmap'].includes(concept))state.seenV=true;
 renderPersistentDiagram();
}
document.addEventListener('keydown',e=>{if((e.key===' ')&&e.target.matches('.build-card')){e.preventDefault();revealDirections(e.target);pinConcept(e.target.dataset.concept,interactiveConcept(e.target));}});
function renderOperation(){
 const staticSquare=isDoubleComplexView()&&['square','square1','square2'].includes(state.effect);
 const context=[state.module,state.step,staticSquare?'square':state.effect,state.annotationStep].join(':');
 if(context!==expositionContext){$('#operationBoard').scrollTop=0;expositionContext=context;}
 const prelude=isDoubleComplexView()&&state.initialReveal<0;
 if(isDoubleComplexView()&&['subcomplex','inclusion'].includes(state.effect))replaceMathContent($('#operationBoard'),filteredSubcomplexExposition({concept:state.effect,math,language}));else if(isDoubleComplexView()&&['graded','gradedmap'].includes(state.effect))gradedProof.render(state);else if(state.module!=='converge')replaceMathContent($('#operationBoard'),prelude?'':operationMarkup(state,language(),math),{animate:!staticSquare});$('#operationBoard').inert=prelude;$('#operationBoard').setAttribute('aria-hidden',String(prelude));
 squareTrace.sync(state.effect,isDoubleComplexView());filtrationSweep.sync(isDoubleComplexView()&&state.effect==='filtration');filtrationTrace.sync(isDoubleComplexView()&&state.effect==='filteredmap');degreeSweep.sync(isDoubleComplexView()&&state.effect==='total');totalTrace.sync(state.effect,isDoubleComplexView());gradedTrace.sync(isDoubleComplexView()&&state.initialReveal===11&&state.effect==='gradedmap');evolution.sync(state);filteredView.sync(state);stabilityView.sync(state);abutmentView.sync(state);
}

// The coordinate frame is mounted once. Only keyed mathematical layers change.
function isTransitionReading(){return !state.cover&&state.module==='converge'&&state.step===0&&state.notePage<2;}
// This explanatory entry keeps the preceding differential page as its visual.
function diagramState(){return isTransitionReading()?{...state,module:'learn',step:5,notePage:1,annotationStep:4,r:Math.max(1,state.r)}:state;}
function fixedDiagram(state=diagramState()){
 const n=state.n,p=state.p,a=state.annotationStep||0,m=state.module,s=state.step;
 let base=svgStart(GRID_MAX,GRID_MAX),end=base.indexOf('</defs>')+7;
 let frame=base.slice(end),edges='',terms='',overlay='',caption='',kind='K',h=false,v=false,filter=false,total=false,selected=false;
 const finite=['lab','trace'].includes(m);
 if(m==='initial'){
  total=['total','totalmap','totalcohom','filtration','filteredmap','subcomplex','inclusion'].includes(state.effect);filter=['filtration','filteredmap','subcomplex','inclusion'].includes(state.effect);h=total?['totalmap','filteredmap','subcomplex'].includes(state.effect):state.seenH;v=total?['totalmap','filteredmap'].includes(state.effect):state.seenV;
  if(state.effect==='graded'){total=true;filter=true;selected=true;h=false;v=false;}
  if(state.effect==='gradedmap'){total=false;filter=false;selected=true;h=false;v=false;}
  if(state.effect==='zeropage'){kind='E_0';h=false;v=false;selected=false;}
  if(s===0)overlay+=relationOverlay(state.effect);
  if(state.initialReveal>=0&&state.initialReveal<=4){
   const {gap,radius,step}=EXTENT,short=2*radius,long=2*step+short;
   const [topX,topY]=xy(2,GRID_MAX),[rightX,rightY]=xy(GRID_MAX,2);
   overlay+=`<g class="extent-ellipsis" aria-label="Displayed window continues">${label(topX,topY-NODE_HALF_H-gap-radius,raw`\cdots`,long,short,true)}${label(rightX+NODE_HALF_W+gap+radius,rightY,raw`\vdots`,short,long,true)}</g>`;
  }
  if(total)caption=raw`${totalDegreeTex(n)}=\bigoplus_{i=0}^{${n}}K^{i,${n}-i}`;
 }else if(m==='learn'){
  if(s<=2){h=s===0||s===1&&a===3;v=h;total=a>0;filter=s>=1;selected=s===2&&a>=2;if(s===2&&a>=3){h=false;v=false;}}
  if(s===0)caption=a===1?raw`Z^{${n}}=\ker(D:C^{${n}}\to C^{${n+1}})`:a===2?raw`B^{${n}}=\operatorname{im}(D:C^{${n-1}}\to C^{${n}})`:raw`H^{${n}}=Z^{${n}}/B^{${n}}`;
  if(s===1&&a>0)caption=raw`F^{${p}}C^{${n}}=\bigoplus_{i=${p}}^{${n}}K^{i,${n}-i}`;
  if(s===2&&a>0)caption=raw`E_0^{${p},${n-p}}\cong K^{${p},${n-p}}`;
  if(s===3){kind=a>=2?'E_1':'E_0';v=a===1;caption=a>=2?raw`E_1^{i,j}\cong H^j(K^{i,\bullet},\delta_2)`:raw`d_0[a]=[Da]=[\delta_2a]`;}
  if(s===4){kind=a>=3?'E_2':'E_1';h=a>=1&&a<3;caption=a>=3?raw`E_2^{i,j}\cong H^i(E_1^{\bullet,j},d_1)`:raw`d_1[a]=[\delta_1a]`;}
  if(s===5){const r=Math.max(1,state.r);kind=a===5?`E_${r+1}`:a>=3?`E_${r}`:'K';if(a>=3)overlay+=label(420,22,raw`r=${r}`,160,32);if(a===4&&1+r<=GRID_MAX&&3-r>=0)edges+=line(...xy(1,2),...xy(1+r,3-r),'r',true,`d_${r}`);if(a<=2){total=true;filter=true;}caption=a<=2?raw`Z_r^{p,q},B_r^{p,q}\subseteq C^{p+q}`:raw`d_r:E_r^{p,q}\to E_r^{p+r,q-r+1}`;}
 }
 if(m==='learn'&&s===6){
  kind='K';h=v=total=filter=selected=false;edges='';
  const Z=a===1,r=Math.max(1,state.r),fromDegree=Z?n:n-1,fromIndex=Z?p:p-r,toDegree=Z?n+1:n,toIndex=Z?p+r:p;
  overlay=`<g class="filtered-source">${diagonal(fromDegree,fromIndex,true,false)}</g><g class="filtered-target-total">${diagonal(toDegree,0,false,false)}</g><g class="next-total filtered-target">${diagonal(toDegree,toIndex,true,false)}</g>`;
  overlay+=label(420,22,a===3?raw`B_{${r}}^{${p},${n-p}}\subseteq Z_s^{${p},${n-p}}\quad(s\ge0)`:raw`F^{${fromIndex}}C^{${fromDegree}}\xrightarrow{D}C^{${toDegree}}\qquad F^{${toIndex}}C^{${toDegree}}`,500,40,true);
 }
 if(m==='converge'){kind='E_0';h=false;v=false;total=false;filter=false;selected=false;}
 if(m==='learn'&&(s===3||s===4)){kind='E_0';h=false;v=!(m==='learn'&&s===3&&state.notePage===0);total=false;filter=false;selected=false;edges='';overlay='';}
 const showNext=(m==='initial'&&['totalmap','filteredmap','subcomplex'].includes(state.effect))||(m==='learn'&&s===0&&a===1)||(m==='learn'&&s===1&&a>=3);
 if(m==='initial'&&state.effect==='inclusion')overlay+=`<g class="total-inclusion-outline">${diagonal(n,0,true,false)}</g>`;
 if(total){overlay+=diagonal(n,filter?p:0,true,false);overlay+=`<g class="source-label">${label(xy(2,GRID_MAX)[0],22,filter?raw`F^{${p}}C^{${n}}${p>n?'=0':''}`:totalDegreeTex(n),filter?150:250,42,true,filter?'':'equals')}</g>`;}
 if(m==='initial'&&state.effect==='graded'||m==='learn'&&s===2&&a>=2)overlay+=`<g class="denominator-region">${diagonal(n,p+1,true,false)}</g>`;
 if(showNext)overlay+=`<g class="next-total">${diagonal(n+1,filter?p:0,true,false)}</g>`;
 if(m==='initial'&&state.effect==='gradedmap'){
  if(p<=n&&p<GRID_MAX)edges+=line(...xy(p,n-p),...xy(p+1,n-p),'h',true,raw`\delta_1`);
  if(p<=n&&n-p<GRID_MAX)edges+=line(...xy(p,n-p),...xy(p,n-p+1),'v',true,raw`\delta_2`);
  else if(p<=n)edges+=continuation(xy(p,n-p)[0],xy(p,n-p)[1]-NODE_HALF_H-5,xy(p,n-p)[0],12,'delta2');
  overlay+=`<g class="source-label">${label(xy(2,GRID_MAX)[0],18,raw`\operatorname{Gr}_F^{${p}}D\;\longleftrightarrow\;\delta_2^{${p},${n-p}}`,420,38,true)}</g>`;
 }
 if(m==='learn'&&s===0&&a===2&&n>0)overlay+=`<g class="next-total">${diagonal(n-1,0,true,false)}</g>`;
 if(m==='initial'&&state.effect==='graded')overlay+=`<g class="target-label">${label(650,22,raw`F^{${p+1}}C^{${n}}`,150,42,true)}</g>`;
 if(showNext)overlay+=`<g class="target-label">${label(filter?650:xy(GRID_MAX,GRID_MAX)[0],22,filter?raw`F^{${p}}C^{${n+1}}`:totalDegreeTex(n+1),filter?150:250,42,true,filter?'':'equals')}</g>`;
 if(!finite){
  for(let i=0;i<=GRID_MAX;i++)for(let j=0;j<=GRID_MAX;j++){
   let activeSource=!total||i+j===(m==='learn'&&s===0&&a===2?n-1:n)&&(!filter||i>=p);
   if(h&&i<GRID_MAX)edges+=`<g class="${activeSource?'':'context-edge'}">${line(...xy(i,j),...xy(i+1,j),'h',true,m==='initial'||j===2&&i===1?(kind==='E_1'?'d_1':'\\delta_1'):'')}</g>`;
   if(v&&j<GRID_MAX)edges+=`<g class="${activeSource?'':'context-edge'}">${line(...xy(i,j),...xy(i,j+1),'v',true,kind==='E_0'?'d_0':m==='initial'||i===1&&j===2?'\\delta_2':'')}</g>`;
   let muted=selected?!(i===p&&i+j===n):total&&(!((i+j===n||showNext&&i+j===n+1)&&(!filter||i>=p)));
   if(m==='learn'&&s===0&&a===2&&i+j===n-1)muted=false;
   if(m==='initial'&&state.effect==='gradedmap')muted=!(p<=n&&(i===p&&(i+j===n||i+j===n+1)||i===p+1&&i+j===n+1));

   if(m==='learn'&&s===6){const from=a===1?n:n-1,to=a===1?n+1:n,first=a===1?p:Math.max(0,p-state.r);muted=!((i+j===from&&i>=first)||i+j===to);}
   terms+=node(i,j,`${kind}^{${i},${j}}`,{muted});
  }
  // Edge-of-window continuations have the same reveal and color rules as their direction.
  for(let k=0;k<=GRID_MAX;k++){
   if(h)edges+=`<g class="${total&&GRID_MAX+k!==n?'context-edge':''}">${continuation(xy(GRID_MAX,k)[0]+62,xy(0,k)[1],xy(GRID_MAX,k)[0]+88,xy(0,k)[1],'delta1')}</g>`;
   if(v)edges+=`<g class="${total&&GRID_MAX+k!==n?'context-edge':''}">${continuation(xy(k,0)[0],43,xy(k,0)[0],17,'delta2')}</g>`;
  }
 }else{
  const c=scene(),r=pageR(),trace=m==='trace';
  if(trace&&s<4){
   for(let type of ['h','v'])for(let [src,tar,k]of c.ex[type]){let x=c.ex.gens.find(g=>g.id===src),y=c.ex.gens.find(g=>g.id===tar);edges+=line(...xy(x.p,x.q),...xy(y.p,y.q),type,true,`\\delta_${type==='h'?1:2}${k<0?'=-1':''}`);}

  }else if(trace&&s===4){edges+=line(...xy(0,1),...xy(2,0),'r',true,'d_2');}else if(m==='lab')for(let i=0;i<=GRID_MAX;i++)for(let j=0;j<=GRID_MAX;j++){
   const src=c.page(r,i,j),tar=c.page(r,i+r,j-r+1);
   if(src.dim&&tar.dim&&rank(c.differential(r,i,j),tar.dim))edges+=line(...xy(i,j),...xy(i+r,j-r+1),r===0?'v':r===1?'h':'r',true,`d_${r}`);
  }
  for(let i=0;i<=GRID_MAX;i++)for(let j=0;j<=GRID_MAX;j++){
   let E=c.page(r,i,j),tex=E.dim===0?'0':`\\mathbb Q${E.dim===1?'':`^{${E.dim}}`}`,dim=E.dim;
   if(trace&&s<4){let gs=c.ex.gens.filter(g=>g.p===i&&g.q===j);dim=gs.length;tex=dim?`\\langle ${gs.map(g=>g.id).join(',')}\\rangle`:'0';}
   terms+=node(i,j,tex,{dim,muted:m==='converge'&&a>0&&(i+j!==n||i<p),active:m==='converge'&&s>=2&&a>0&&i===p&&j===n-p});
  }
  if(m==='lab')caption=raw`E_${r}^{i,j},\quad d_${r}:(i,j)\longmapsto(i+${r},j${1-r<0?'':'+'}${1-r})`;
 }
 // Full formulas belong to the readable operations panel, not a tiny SVG caption.
 return base.slice(0,end)+`<g id="coordinate-frame">${frame}</g><g id="diagram-overlays">${overlay}</g><g id="diagram-edges">${edges}</g><g id="diagram-terms">${terms}</g></svg>`;
}
function renderPersistentDiagram(){
 const host=$('#diagram'),holder=document.createElement('div');holder.innerHTML=fixedDiagram();const desired=holder.firstElementChild;
 if(!host.firstElementChild){host.append(desired);syncDiagramLabels();syncCoordinatePresentation();observeDiagramSize();return;}
 const current=host.firstElementChild;
 for(const id of ['diagram-overlays','diagram-edges','diagram-terms'])syncGraphChildren(current.querySelector('#'+id),desired.querySelector('#'+id));
 current.querySelector('#graphTitle').textContent=desired.querySelector('#graphTitle').textContent;syncDiagramLabels();syncCoordinatePresentation();
}
function statementFormulas(){return document.querySelectorAll('.formal-statement.is-active .reading-formula');}
// Diagram action IDs stay stable even when auxiliary formulas move to the exposition.
function annotationCount(){return Math.max(0,...[...document.querySelectorAll(`[data-statement="${activeStatementKey()}"] .reading-formula`)].map(el=>Number(el.dataset.annotation)));}
function updateAnnotations(){
 if(state.cover||isDoubleComplexView())return;
 const a=state.annotationStep||1;
 $('#actionTabs').innerHTML=actionNames(state,language()).map((name,i)=>`<button data-action="${i+1}" aria-pressed="${a===i+1}">${mathControlLabel(name)}</button>`).join('');
 const elements=[...statementFormulas()];
 elements.forEach(el=>{el.classList.toggle('annotation-seen',Number(el.dataset.annotation)===a);el.classList.add('definition-current');});
 const key=activeStatementKey(),last=Math.max(revealedReadings.get(key)??-1,state.notePage);revealedReadings.set(key,last);
 syncReadingEntries(key);
 renderQuickCheck();window.spectralState={...state,language:language()};renderOperation();
}
function setAnnotation(i){state.stackR=null;state.annotationStep=Math.max(1,Math.min(annotationCount(),i));renderPersistentDiagram();updateAnnotations();translatePage();}
function revealAnnotation(el){if(state.cover||isDoubleComplexView())return;const formula=el.closest('.formal-statement .reading-formula');if(formula){const card=formula.closest('[data-statement]');if(card&&!card.classList.contains('is-active'))activateStatement(card.dataset.statement);setAnnotation(Number(formula.dataset.annotation));}}


// Explicit dot bounds avoid font-dependent whitespace in the two orientations.
// The existing label plane still owns their scaling and delayed entrance.
function extentDots(tex){
 const {radius,step}=EXTENT,horizontal=tex===raw`\cdots`,short=2*radius,long=2*step+short;
 const width=horizontal?long:short,height=horizontal?short:long;
 return `<svg viewBox="0 0 ${width} ${height}" width="100%" height="100%" aria-hidden="true">${[0,1,2].map(i=>`<circle cx="${radius+(horizontal?i*step:0)}" cy="${radius+(horizontal?0:i*step)}" r="${radius}" fill="currentColor"/>`).join('')}</svg>`;
}
// Keep HTML math out of SVG foreignObject: WebKit must scale the whole label plane once.
function syncDiagramLabels(){
 const host=$('#diagram');let plane=host.querySelector('.diagram-label-plane');
 if(!plane){plane=document.createElement('div');plane.className='diagram-label-plane';plane.setAttribute('aria-hidden','true');host.append(plane);}
 const old=new Map([...plane.children].map(el=>[el.dataset.key,el]));
 for(const anchor of host.querySelectorAll('svg .math-anchor')){
  const d=anchor.dataset,key=[d.x,d.y,d.width,d.height].join(':'),el=old.get(key)||document.createElement('div');old.delete(key);
  el.className='diagram-label'+(anchor.closest('.node')?' term-label':'')+(d.small==='true'?' small-label':'')+(anchor.closest('.diagram-caption')?' caption-label':'')+(anchor.closest('.source-label')?' source-label':'')+(anchor.closest('.target-label')?' target-label':'')+(anchor.closest('.extent-ellipsis')?' extent-label':'');el.dataset.key=key;el.classList.toggle('relation-aligned',d.align==='equals');
  const map=anchor.previousElementSibling?.matches('.arrow')?anchor.previousElementSibling:null;if(map){el.classList.add('map-label',map.classList.contains('h')?'map-h':map.classList.contains('v')?'map-v':'map-r');el.dataset.mapConcept=map.dataset.concept;}else delete el.dataset.mapConcept;
  el.style.left=d.x+'px';el.style.top=d.y+'px';el.style.width=d.width+'px';el.style.height=d.height+'px';
  el.style.opacity=`calc(${anchor.closest('.muted')?'var(--graph-muted-opacity)':1} * ${anchor.closest('.zero')?'var(--graph-zero-opacity)':1} * ${anchor.closest('.context-edge')?'var(--graph-context-opacity)':1})`;
  const changed=el.dataset.tex!==d.tex;if(changed){if(anchor.closest('.node'))replaceBigradedLabel(el,d.tex,math);else replaceMathContent(el,anchor.closest('.extent-ellipsis')?extentDots(d.tex):math(d.tex));el.dataset.tex=d.tex;}
  if(!el.isConnected){plane.append(el);fadeGraphAddition(el);}
  alignDiagramRelation(el);
 }
 for(const el of old.values())el.remove();
}
function observeDiagramSize(){
 const viewport=$('.diagram-viewport'),host=$('#diagram');
 const fit=()=>{fitDiagramSurface(viewport,host,'--diagram-scale');host.querySelectorAll('.relation-aligned').forEach(alignDiagramRelation);};
 fitDiagram=fit;diagramResizeObserver=new ResizeObserver(fit);diagramResizeObserver.observe(viewport);fit();
}

function relationOverlay(effect){
 if(!['square1','square2','totalsquare','anticommute'].includes(effect))return '';
 const edge=(p,q,p1,q1,type,order)=>`<g class="relation-route route-${order}">${line(...xy(p,q),...xy(p1,q1),type,true)}</g>`;
 let out='';
 if(effect==='totalsquare'){const {p,q}=differentialOrigin();out+=edge(p,q,p+1,q,'h',1)+edge(p,q,p,q+1,'v',1)+edge(p+1,q,p+2,q,'h',2)+edge(p+1,q,p+1,q+1,'v',2)+edge(p,q+1,p+1,q+1,'h',2)+edge(p,q+1,p,q+2,'v',2);}
 else if(effect==='square1'||effect==='square2'){
  const horizontal=effect==='square1',end=horizontal?[3,1]:[1,3];
  out+=edge(1,1,horizontal?2:1,horizontal?1:2,horizontal?'h':'v',1);
  out+=edge(horizontal?2:1,horizontal?1:2,...end,horizontal?'h':'v',2);

 }else{
  const {p,q}=differentialOrigin(effect);
  out+=edge(p,q,p+1,q,'h',1)+edge(p+1,q,p+1,q+1,'v',2)+edge(p,q,p,q+1,'v',1)+edge(p,q+1,p+1,q+1,'h',2);
 }
 return `<g class="relation-overlay ${effect.includes('square')?'square-route':''}">${out}</g>`;
}

// Typesetting is part of total progress: count completed font faces, font-set
// layout readiness, and the two painted frames before allowing entry.
(async()=>{
 const fonts=[...document.fonts].filter(f=>f.family.includes('KaTeX')||f.status==='loading');
 let completed=0;const total=fonts.length+3;
 const report=()=>window.spectralBoot?.progress(65+35*completed/total,'排版数学公式','Typesetting mathematics');
 report();
 const loaded=await Promise.allSettled(fonts.map(async font=>{await font.load();completed++;report();}));
 if(loaded.some(f=>f.status==='rejected')){window.spectralBoot?.fail();return;}
 await document.fonts.ready;completed++;report();
 for(let i=0;i<2;i++){await new Promise(requestAnimationFrame);completed++;report();}
 window.spectralBoot?.ready();syncInitialEntrance();
})().catch(()=>window.spectralBoot?.fail());



function syncCoordinatePresentation(){
 const graph=$('#diagram'),frameOnly=state.module==='initial'&&state.initialReveal<0;
 const symbolic=['initial','learn','converge'].includes(state.module)&&!frameOnly;
 graph.classList.toggle('is-page-grid',state.module!=='initial');
 graph.classList.toggle('frame-only',frameOnly);graph.classList.toggle('symbolic-coordinates',symbolic);
 graph.querySelectorAll('.axis-tick').forEach(tick=>{
  const v=Number(tick.dataset.value),horizontal=tick.dataset.axis==='p',close=(frameOnly||symbolic)&&v>=0;
  if(horizontal){tick.setAttribute('x',xy(v,0)[0]-(close&&v===0?10:0));tick.setAttribute('y',xy(0,0)[1]+(close?20:38));}
  else{tick.setAttribute('x',xy(0,0)[0]-(close?12:56));tick.setAttribute('y',xy(0,v)[1]+5);}
  tick.setAttribute('aria-hidden',String(symbolic&&v>=0));tick.classList.toggle('redundant-coordinate',symbolic&&v>=0);
 });
 graph.querySelector('#diagram-terms').setAttribute('aria-hidden',String(frameOnly));
 graph.querySelectorAll('.node:not(.outside-quadrant)').forEach(node=>node.setAttribute('tabindex',frameOnly?'-1':'0'));
}

function releaseEmphasis(animation){
 const el=animation.effect?.target;
 if(!el?.isConnected||animation.playState==='finished'||matchMedia('(prefers-reduced-motion:reduce)').matches){animation.cancel();return;}
 const from=getComputedStyle(el).opacity;animation.cancel();const to=getComputedStyle(el).opacity;
 if(from!==to)el.animate([{opacity:from},{opacity:to}],{duration:220,easing:'ease-out'});
}

// One finite emphasis per definition stage. Geometry and the right pane stay fixed.
function emphasizeCurrentDefinition(){
 const stage=$('#stage'),initialView=isDoubleComplexView();
 const key=state.cover?'cover':initialView?`initial:${state.initialReveal}`:`${state.module}:${state.step}:${state.annotationStep}`;

 stage.dataset.definitionKey=key;definitionAnimations.forEach(releaseEmphasis);definitionAnimations=[];
 if(state.cover||matchMedia('(prefers-reduced-motion:reduce)').matches)return;
 let targets=[];
 targets=[...document.querySelectorAll('.has-evolution #pageEvolution .evolution-page.is-current .evolution-dot,.has-evolution #pageEvolution .evolution-page.is-current .evolution-differential,.has-stability-view .stability-node.central,.has-abutment-view .abutment-term.chosen,#diagram .concept-active')].filter(el=>el.getClientRects().length);
 if(initialView&&['delta1','delta2'].includes(initialConcept()))targets.push(...document.querySelectorAll(`#diagram .map-label[data-map-concept="${initialConcept()}"]`));
 if(!targets.length)targets=[...document.querySelectorAll('#diagram .arrow:not(.context-edge),#diagram .diag-box')];
 if(!targets.length)targets=[...document.querySelectorAll('#diagram .node:not(.muted) .node-bg')];
 targets.forEach(el=>{
  if(el.closest('.outside-quadrant'))return;
  const from=getComputedStyle(el).opacity,delay=el.closest('.route-2')?150:0;
  el.getAnimations().forEach(a=>a.cancel());const opacity=restingOpacity(el);
  const animation=el.animate([{opacity:from},{opacity:1,offset:.45},{opacity}],{duration:650,delay,easing:'ease-out',iterations:1});
  definitionAnimations.push(animation);
 });
 stage.dataset.emphasisCount=String(Number(stage.dataset.emphasisCount||0)+1);
}

// Called after diagram reconciliation, so SVG and HTML math start together.
function syncInitialEntrance(){
 if(document.body.getAttribute('aria-busy')!=='false')return;
 initialAnimations.sync({active:isDoubleComplexView()&&state.initialReveal>=0,step:state.initialReveal,seenH:state.seenH,seenV:state.seenV});
}

// Legacy graded controls select the same two stages as the left-hand entry.
document.addEventListener('click',event=>{const button=event.target.closest('[data-graded-view]');if(!button)return;event.stopPropagation();selectInitialBuild(11,button.dataset.gradedView==='differential'?1:0);});

function playbackKey(){return state.cover||isTransitionReading()?null:isDoubleComplexView()?(state.initialReveal<0?null:`initial:${state.initialReveal}:${state.totalStep}:${state.filtrationStep}:${state.initialReveal===11?state.gradedMode:''}`):`${state.module}:${state.step}:${state.notePage}`;}
function playbackKind(){
 if(isDoubleComplexView())return [0,1,2,7,9,10].includes(state.initialReveal)||state.initialReveal===11&&state.gradedMode==='space'?'entrance':'demonstration';
 return state.module==='learn'&&(state.step===6||state.step===5&&state.notePage===0||state.step===4&&state.notePage===0)||state.module==='converge'&&state.step===0&&state.notePage===2?'demonstration':'entrance';
}
function syncPlayback(){playback.sync({key:playbackKey(),kind:playbackKind(),hasEntrance:state.module==='learn'&&state.step===6&&state.notePage===0});}
async function playCurrentEntrance({waitUntil}){
 if(isDoubleComplexView()&&state.initialReveal<=2){
  initialAnimations.play(state.initialReveal);await waitUntil(()=>!initialAnimations.isPlaying());
 }else if(state.module==='learn'&&state.step===6&&state.notePage===0){filteredView.enter();await waitUntil(()=>!filteredView.isPlaying());}
 else{emphasizeCurrentDefinition();await Promise.all(definitionAnimations.map(a=>a.finished.catch(()=>{})));}
}

function stopDiagramAnimation(){
 pageFormation.clear();squareTrace.clear();totalTrace.clear();gradedTrace.clear();filtrationTrace.clear();degreeSweep.stop();filtrationSweep.stop();initialAnimations.clear();filteredView.stop();stabilityView.clear();evolution.clear();
 definitionAnimations.forEach(releaseEmphasis);definitionAnimations=[];
}
async function playCurrentAnimation({signal,waitUntil,wait}){
 const live=()=>!signal.aborted;
 const run=async(action,isPlaying)=>{if(!live())return false;action();return waitUntil(()=>!isPlaying());};
 if(isDoubleComplexView()){
  const concept=state.pinned||initialConcept(),index=state.initialReveal;
  if(index<=2){if(index>0)await run(()=>totalTrace.play(concept,true),totalTrace.isPlaying);}
  else if(index===3){
   for(const c of concept==='square1'||concept==='square2'?[concept]:['square1','square2']){
    if(!live())return;applyConcept(c);await squareTrace.play(c,squareCentres(c));if(!live())return;if(c==='square1'&&!await wait(visualMotion().hold))return;
   }
  }else if(['anticommute','totalmap','totalsquare','delta1','delta2'].includes(concept))await run(()=>totalTrace.play(concept,true),totalTrace.isPlaying);
  else if(concept==='total')await degreeSweep.play(true);
  else if(concept==='filtration'){
   await filtrationSweep.play(true);
  }else if(concept==='filteredmap')await run(()=>filtrationTrace.play(true),filtrationTrace.isPlaying);
  else if(concept==='gradedmap')await run(()=>gradedTrace.play(true),gradedTrace.isPlaying);
  else {emphasizeCurrentDefinition();await Promise.all(definitionAnimations.map(a=>a.finished.catch(()=>{})));}
 }else if(state.module==='learn'&&state.step===5&&state.notePage===0)await pageFormation.play(Math.max(1,state.r));
 else if(state.module==='learn'&&state.step===6)await run(()=>filteredView.play(),filteredView.isPlaying);
 else if(state.module==='learn'&&state.step===4&&state.notePage===0)await evolution.play();
 else if(state.module==='converge'&&state.step===0&&state.notePage===2)await run(()=>stabilityView.play(),stabilityView.isPlaying);
 else {emphasizeCurrentDefinition();await Promise.all(definitionAnimations.map(a=>a.finished.catch(()=>{})));}
}
// Selecting an entry rearms automatically through its reading key. Clicking the
// current demonstration explicitly rearms after dismissal or with autoplay off.
// An entrance is tied to entry, so clicking its current card does not replay it.
$('#explanation').addEventListener('click',event=>{
 if(event.target.closest('[data-toggle-build],[data-toggle-reading],[data-toggle-statement],[data-toggle-section],[data-zoom]'))return;
 const entry=event.target.closest('.build-card,.numbered-entry');if(!entry)return;
 queueMicrotask(()=>{if(entry.classList.contains('build-current'))playback.restart(true);});
});
