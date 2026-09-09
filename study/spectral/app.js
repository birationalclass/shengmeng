import {Complex,examples,texVector,matrixTex,q,rank,basisVector} from './algebra.js';
import {lessons,convergence,initial,totalCohomology} from './content.js?v=19';
import {translatePage,language,toggleLanguage} from './language.js?v=19';
import {operationMarkup,viewNames,actionNames} from './workbench.js?v=19';
import {pageStackMarkup} from './page-stack.js?v=19';
const $=s=>document.querySelector(s),raw=String.raw;
const GRID_MAX=4, INITIAL_STEPS=8;
const NODE_HALF_W=34,NODE_HALF_H=19;
const state={module:'initial',cover:true,initialReveal:-1,annotationStep:1,diagramMode:'3d',stackR:null,stackStart:0,seenH:false,seenV:false,effect:null,pinned:null,pinnedKey:null,step:0,n:3,p:1,r:0,direction:'both',example:'survive',lambda:0,selected:null};
let diagramResizeObserver=null,definitionAnimations=[],definitionScrollFrame=0;const complexes=Object.fromEntries(Object.entries(examples).map(([k,x])=>[k,new Complex(x)]));
const traceComplex=new Complex({...examples.d2,gens:[...examples.d2.gens,{id:'x',p:0,q:0},{id:'y',p:0,q:1}],v:[...examples.d2.v,['x','y',1]]});
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const math=(tex,display=false)=>katex.renderToString(tex,{displayMode:display,throwOnError:true,strict:'error',trust:false});
const block=(t,concept='')=>`<div class="math-block" data-formula="${esc(t)}" ${concept?`data-concept="${concept}"`:''} role="button" tabindex="0" aria-label="${concept?'悬停对照，点击固定高亮':'放大查看公式'}">${math(t,true)}<button class="formula-zoom" data-zoom aria-label="放大查看公式" title="点击放大公式">↗</button></div>`;
const scene=()=>state.module==='trace'?traceComplex:complexes[state.example];
const pageR=()=>state.module==='trace'&&state.step>=4?state.step-2:state.r;
const stepCount=()=>({initial:initial.length,learn:lessons.length-1,lab:scene().maxP+3,trace:6,converge:convergence.length})[state.module];
let layout={dx:125,dy:75};
const xy=(p,q)=>[225+p*layout.dx,370-q*layout.dy];
const shifted=(s,k)=>k===0?s:`${s}${k>0?'+':''}${k}`;
function label(x,y,tex,w=116,h=38,small=false){return `<g class="math-anchor" data-x="${x-w/2}" data-y="${y-h/2}" data-width="${w}" data-height="${h}" data-small="${small}" data-tex="${esc(tex)}"><title>${esc(tex)}</title></g>`;}
function line(x1,y1,x2,y2,type,hot,tex=''){let dx=x2-x1,dy=y2-y1,len=Math.hypot(dx,dy),pad=Math.min(dx===0?Infinity:NODE_HALF_W*len/Math.abs(dx),dy===0?Infinity:NODE_HALF_H*len/Math.abs(dy))+5;const f=pad/len;x1+=dx*f;y1+=dy*f;x2-=dx*f;y2-=dy*f;let out=`<path data-concept="${arrowConcept(type)}" tabindex="0" role="button" aria-label="${arrowConcept(type)}" class="arrow ${type} ${hot?'hot':''} " d="M${x1},${y1} L${x2},${y2}" marker-end="url(#arrow-${type})"/>`;if(tex){const compact=['\\delta_1','\\delta_2','d_0','d_1'].includes(tex);out+=label((x1+x2)/2+(dx===0?(compact?23:26):0),(y1+y2)/2+(dy===0?(compact?-14:-17):0),tex,compact?36:68,compact?20:24,true);}return out;}
function svgStart(maxP=GRID_MAX,maxQ=GRID_MAX){
 layout={dx:500/maxP,dy:300/maxQ};
 const [originX,originY]=xy(0,0);
 let out=`<svg viewBox="0 0 840 525" role="img" aria-labelledby="graphTitle"><title id="graphTitle">${esc($('#sceneTitle').textContent)}；横轴第一指标，纵轴第二指标</title><defs>`;
 for(const [id,color] of [['h','#71e2d0'],['v','#8fbeff'],['r','#f4c876'],['continuation','#8da7ae'],['axis','#78939d']])out+=`<marker id="arrow-${id}" markerUnits="userSpaceOnUse" markerWidth="10" markerHeight="10" viewBox="0 0 10 10" refX="8" refY="5" orient="auto"><path d="M2,1.75 L8,5 L2,8.25" fill="none" stroke="${color}" stroke-width="1.35" stroke-linecap="round" stroke-linejoin="round"/></marker>`;
 // The axes cross at the centre of the (0,0) term. Mask their portions behind
 // terms so even dimmed/zero nodes retain unobstructed mathematical labels.
 out+='<mask id="coordinate-axis-mask" maskUnits="userSpaceOnUse" x="0" y="0" width="840" height="525"><rect width="840" height="525" fill="white"/>';
 const maskTerm=(p,q)=>{const [x,y]=xy(p,q);return `<rect x="${x-NODE_HALF_W-4}" y="${y-NODE_HALF_H-4}" width="${2*NODE_HALF_W+8}" height="${2*NODE_HALF_H+8}" rx="8" fill="black"/>`;};
 for(let p=0;p<=maxP;p++)out+=maskTerm(p,0);
 for(let q=0;q<=maxQ;q++)if(q!==0)out+=maskTerm(0,q);
 out+='</mask><linearGradient id="node-glass" x1="0" y1="0" x2="1" y2="1"><stop stop-color="#80b7bd" stop-opacity=".19"/><stop offset=".45" stop-color="#47747e" stop-opacity=".14"/><stop offset="1" stop-color="#213c47" stop-opacity=".32"/></linearGradient></defs>';
 for(let p=0;p<=maxP;p++){
  const [x]=xy(p,0);
  if(p!==0)out+=`<path class="grid" d="M${x},38 V${originY+20}"/>`;
  out+=`<text class="axis-text axis-tick" data-axis="p" data-value="${p}" x="${x}" y="${originY+38}" text-anchor="middle">${p}</text>`;
 }
 for(let q=0;q<=maxQ;q++){
  const [,y]=xy(0,q);
  if(q!==0)out+=`<path class="grid" d="M${originX-40},${y} H795"/>`;
  if(q!==0)out+=`<text class="axis-text axis-tick" data-axis="q" data-value="${q}" x="${originX-56}" y="${y+5}" text-anchor="end">${q}</text>`;
 }
 out+=`<g class="coordinate-axes" data-origin-x="${originX}" data-origin-y="${originY}" mask="url(#coordinate-axis-mask)"><path id="p-axis" class="coordinate-axis" d="M${originX-45},${originY} H825" marker-end="url(#arrow-axis)"/><path id="q-axis" class="coordinate-axis" d="M${originX},${originY+32} V8" marker-end="url(#arrow-axis)"/></g><text class="axis-text axis-name" x="827" y="${originY-11}">p</text><text class="axis-text axis-name" x="${originX-17}" y="17">q</text>`;
 return out;
}
function node(p,qv,tex,{dim,muted=false,active=false}={}){let [x,y]=xy(p,qv);return `<g data-concept="space" class="node ${muted?'muted':''} ${active?'trace-active':''} ${state.selected?.p===p&&state.selected?.q===qv?'selected':''} ${dim===0?'zero':''}" role="button" tabindex="0" data-p="${p}" data-q="${qv}" aria-label="位置 (${p},${qv})${dim!==undefined?`, 维数 ${dim}`:''}"><rect class="node-bg" x="${x-NODE_HALF_W}" y="${y-NODE_HALF_H}" width="${2*NODE_HALF_W}" height="${2*NODE_HALF_H}" rx="9"/>${label(x,y,tex,67,36,tex.length>28)}</g>`;}
function diagonal(n,p,box=true,showLabel=true){
 const first=Math.max(0,p,n-GRID_MAX),last=Math.min(n,GRID_MAX);if(first>last)return '';
 const [x1,y1]=xy(first,n-first),[x2,y2]=xy(last,n-last),length=Math.hypot(x2-x1,y2-y1),angleLength=length||Math.hypot(layout.dx,layout.dy);
 const ux=(length?x2-x1:layout.dx)/angleLength,uy=(length?y2-y1:layout.dy)/angleLength;
 const points=[[-62,-46],[length+62,-46],[length+62,46],[-62,46]].map(([a,b])=>`${Math.max(5,Math.min(835,x1+ux*a-uy*b))},${Math.max(5,Math.min(518,y1+uy*a+ux*b))}`).join(' ');
 let out=box?`<polygon data-concept="filtration" class="diag-box" points="${points}"/>`:'';
 const lineStart=Math.max(0,n-GRID_MAX);out+=`<path class="diag" d="M${xy(lineStart,n-lineStart).join(',')} L${xy(last,n-last).join(',')}"/>`;
 if(showLabel)out+=label(700,17,raw`i+j=${n}`,120,24,true);return out;
}
const formulas=(fs,concepts=[])=>fs.map((t,i)=>block(t,concepts[i]||'')).join('');
function companion(item){if(isDoubleComplexView()){doubleComplexCompanion(item);return;}const meta=statementMeta();$('#sceneKicker').textContent=sectionName();$('#sceneTitle').textContent=state.module==='initial'?'Initial data':state.module==='converge'?'Convergence':state.module==='lab'?'Examples':state.module==='trace'?'Representatives':'Induced structures';$('#explanation').innerHTML=`<article class="formal-statement"><div class="statement-heading"><span>${meta.kind}</span><span class="statement-number">${meta.number}</span></div><h3>${meta.name||item.title}</h3>${meta.intro?`<p class="formal-intro">${meta.intro}</p>`:''}${formulas(item.f,meta.concepts)}</article><div class="slide-supplement"><p>${item.text}</p><details><summary>展开数学理由</summary><p>${item.proof}</p></details></div>`;$('#sceneNote').textContent=item.note;}
function labCompanion(){let c=scene(),r=state.r;let stable=r>=c.maxP+1;companion({title:stable?`E${r}：已经稳定`:`第 ${r} 页 · ${examples[state.example].name}`,tag:'EXACT RATIONAL COMPUTATION',f:[r===0?raw`E_0^{p,q}=\operatorname{Gr}_F^pC^{p+q}\cong K^{p,q}`:raw`E_${r}^{p,q}=\frac{Z_${r}^{p,q}}{Z_{${r-1}}^{p+1,q-1}+B_{${r-1}}^{p,q}}`,raw`d_${r}:E_${r}^{p,q}\to E_${r}^{${shifted('p',r)},${shifted('q',1-r)}}`],text:examples[state.example].description+' 点击任意节点查看代表元、微分矩阵以及本位置的核和像。',note:'用本页的 r 滑块切换谱序列页，从同一总复形的 Zᵣ、Bᵣ 商空间计算。上同调类使用 [a]ᵣ；所列基是计算选择，不是典范分裂。',proof:'计算全部在 ℚ 上进行，分数约分后精确运算。每页检验 dᵣ²=0，下一页维数等于本页核维数减去入射像维数，并独立计算总上同调。'});let summary='<table class="data-table"><tr><th>n</th><th>dim Hⁿ(C)</th><th>Σ dim E∞ᵖⁿ⁻ᵖ</th></tr>';for(let n=0;n<=c.maxN;n++){let H=c.cohomology(n).dim,sum=0;for(let p=0;p<=n;p++)sum+=c.page(c.maxP+2,p,n-p).dim;summary+=`<tr><td>${n}</td><td>${H}</td><td>${sum}</td></tr>`;}$('#explanation').insertAdjacentHTML('beforeend',summary+'</table><p class="badge">由总微分独立核对</p>');let data=c.ex.gens.map(g=>block(raw`${g.id}\in K^{${g.p},${g.q}}`)).join(''); for(let kind of ['h','v'])data+=c.ex[kind].map(([a,b,k])=>block(raw`\delta_${kind==='h'?1:2}${a}=${k===1?'':k===-1?'-':k}${b}`)).join(''); $('#explanation').insertAdjacentHTML('beforeend',`<details><summary>例子的全部生成元与微分</summary>${data}<p>每个列出的生成元为一个基向量；所有未列出的空间及微分值为零。</p></details>`);}
function traceCompanion(){const L=state.lambda,rep=L===0?'b':`b${L>0?'+':''}${L}y`;let items=[
{title:'选择同一个 E₁ 类的代表元',f:[raw`\delta_2x=y,\quad \delta_2b=0`,raw`a_0=${rep}`,raw`a_0-b=\delta_2(${L}x)`],text:'加入一个垂直边界不会改变 E₁ 中的类。调节 λ，观察 a₀=b+λy 是不同上链，却代表同一个垂直上同调类。'},
{title:'横向微分产生一个可消去的项',f:[raw`\delta_1a_0=u`,raw`u=-\delta_2c`,raw`d_1[a_0]=[u]=0`],text:'δ₁a₀ 本身不为零，但它是垂直边界，因此在 E₁ 上为零。该类是 d₁-闭的。'},
{title:'加入修正项 a₁=c',f:[raw`a_1=c\in K^{1,0}`,raw`\delta_1a_0+\delta_2a_1=u-u=0`],text:'修正项 c 向右一列、向下一行，总次数保持为 1。它抵消了 D(a₀) 在第一列中的分量。'},
{title:'总微分只剩右边第二列',f:[raw`a=a_0+a_1=${rep}+c`,raw`Da=z\in K^{2,0}`],text:'施加的始终是 D=δ₁+δ₂。抵消之后，残余项位于相隔两列的位置，给出了第二微分。'},
{title:'得到非零的 d₂',f:[raw`d_2:E_2^{0,1}\to E_2^{2,0}`,raw`d_2[a_0+c]_2=[z]_2\ne0`],text:'源和靶都是一维空间，d₂ 是同构。这里 [a₀+c]₂ 是总上链代表元在第二页商空间中的类。'},
{title:'第三页：两个类都不再贡献',f:[raw`E_3^{0,1}=E_3^{2,0}=0`,raw`H^*(C,D)=0`],text:'源上的类不是 d₂-闭的；靶上的类是 d₂-边界。它们以不同原因在下一页为零，不能笼统理解为两个点被动画删除。'}];let item=items[state.step];companion({...item,tag:'FOLLOW A REPRESENTATIVE',note:'本模块使用 d₂ 例子，另加 x→y 的垂直可缩复形。改变 λ 只改变代表元，不改变各页或最终答案。',proof:'新增生成元 x∈K⁰⁰、y∈K⁰¹ 满足 δ₂x=y，其余涉及 x、y 的微分为零。因此它们组成一个垂直可缩直和因子，既不改变 E₁ 及后续各页，也不改变总上同调。'});}
function inspect(){if(state.module==='converge'){$('#inspector').innerHTML=block(raw`\theta^{p,q}([a]_\infty)=[a]_H+F^{p+1}H^{p+q}`)+'<p>'+ui('这里使用一般理论。有限维数与矩阵请在诱导信息中的精确例子查看。','This is the general construction. Exact dimensions and matrices are available in the examples within Induced structures.')+'</p>';return;}if(state.module==='learn'&&state.step===0){$('#inspector').innerHTML=block(raw`\operatorname{im}(D:C^{n-1}\to C^n)\subseteq\ker(D:C^n\to C^{n+1})`)+block(raw`[a]_H=[a+Db]_H`);return;}if(state.module==='initial'){$('#inspector').innerHTML=block(raw`K^{p,q}\xrightarrow{\delta_1}K^{p+1,q}`)+block(raw`K^{p,q}\xrightarrow{\delta_2}K^{p,q+1}`)+'<p>图中 p、q 是一般指标；虚线延续箭头表示还有未展开的行列，不表示零空间。</p>';return;}const {p,q:qv}=state.selected||{p:['learn','converge'].includes(state.module)?state.p:0,q:['learn','converge'].includes(state.module)?state.n-state.p:1};if(state.module==='learn'){let s=state.step+1,tex=raw`K^{${p},${qv}}`;let text=`第一指标为 ${p}，第二指标为 ${qv}，总次数为 ${p+qv}。`;if(s===3){tex=raw`E_0^{${p},${qv}}\cong K^{${p},${qv}}`;text+=' 同构由取该列分量给出。';}if(s===4){tex=raw`E_1^{${p},${qv}}=H^{${qv}}(K^{${p},\bullet},\delta_2)`;text+=' 这里已经对垂直方向求过上同调。';}if(s===5){tex=raw`E_2^{${p},${qv}}`;text+=' '+ui('已经取过 d₁ 上同调。','Cohomology of d₁ has been taken.');}if(s===6){tex=raw`E_r^{${p},${qv}}`;text+=' 微分靶为 (p+r,q−r+1)。';}$('#inspector').innerHTML=block(tex)+`<p>${text}</p>`;return;}
const c=scene();if(state.module==='trace'&&state.step<4){let gs=c.ex.gens.filter(g=>g.p===p&&g.q===qv);$('#inspector').innerHTML=block(raw`K^{${p},${qv}}=\langle ${gs.map(g=>g.id).join(',')||'0'}\rangle`)+`<p>图中节点是该位置的整个空间；方程中的 b、c、x、y、u、z 是选定基向量。</p>`;return;}
let r=pageR(),E=c.page(r,p,qv),tar=c.page(r,p+r,qv-r+1),M=c.differential(r,p,qv),incoming=c.differential(r,p-r,qv+r-1),outRank=rank(M,tar.dim),inRank=rank(incoming,E.dim),name=state.module==='converge'?'\\infty':r;
let html=block(raw`E_{${name}}^{${p},${qv}}\cong\mathbb Q^{${E.dim}}`);if(E.dim)html+=`<p>选定的商空间基（总上链代表元）：</p>`+E.reps.map(v=>block(raw`[${texVector(v,c.basis(E.n))}]_{${name}}`)).join('');html+=`<p>分子维数 ${E.Z.length}；分母维数 ${E.den.length}。商空间维数 ${E.dim}。</p>`;
if(state.module==='lab'||state.module==='trace'){html+=`<p>微分矩阵：列对应上面的源基，行对应靶的商空间基。</p>`+block(raw`[d_${r}]=${matrixTex(M,tar.dim)}`);html+=`<p>靶位置 (${p+r},${qv-r+1})。靶基：</p>`+block(tar.reps.length?tar.reps.map(v=>raw`[${texVector(v,c.basis(tar.n))}]_${r}`).join(',\;'):raw`\varnothing`);html+=`<p>dim ker d${r} = ${E.dim-outRank}<br>dim im（入射 d${r}）= ${inRank}<br>下一页本位置维数 = ${E.dim-outRank-inRank}</p>`;}else if(E.dim){html+=block(raw`\theta([a]_\infty)=[a]_H+F^{${p+1}}H^{${E.n}}`);}$('#inspector').innerHTML=html;}
function controls(){let html='';$('#controls').inert=false;$('#controls').style.visibility='';if(state.module==='initial'||state.module==='learn'&&state.step===0)html+=`<label>示例总次数 n <input id="nRange" type="range" min="0" max="4" value="${state.n}"><output>${state.n}</output></label>`;if(state.module==='converge'||(state.module==='learn'&&state.step>=1&&state.step<=2)){html+=`<label>示例总次数 n <input id="nRange" type="range" min="0" max="4" value="${state.n}"><output>${state.n}</output></label><label>滤过 p <input id="pRange" type="range" min="0" max="${state.n+1}" value="${state.p}"><output>${state.p}</output></label>`;}if(state.module==='initial'&&state.initialReveal>=7)html+=`<label>滤过 p <input id="pRange" type="range" min="0" max="${state.n+1}" value="${state.p}"><output>${state.p}</output></label>`;if(state.module==='lab'||state.module==='trace'){html+=`<label>例子 <select id="exampleSelect">${Object.entries(examples).map(([k,e])=>`<option value="${k}" ${k===state.example?'selected':''}>${e.name}</option>`).join('')}</select></label>`;}if(state.module==='lab')html+=`<label>页数 r <input id="rRange" type="range" min="0" max="${scene().maxP+2}" value="${state.r}"><output>${state.r}</output></label>`;if(state.module==='trace')html+=`<label>代表元参数 λ <input id="lambdaRange" type="range" min="-2" max="2" value="${state.lambda}"><output>${state.lambda}</output></label><span>${math(raw`a_0=b+\lambda y`)}</span>`;if(state.module==='learn'&&state.step===5||state.module==='converge'&&state.step===1)html+=`<label>r <input id="rRange" type="range" min="1" max="${state.module==='converge'?state.n+2:3}" value="${Math.max(1,state.r)}"><output>${Math.max(1,state.r)}</output></label>`;$('#controls').innerHTML=html;}
function render(updateControls=true){if(state.module==='initial')companion(initial[state.step]);if(state.module==='learn')companion(state.step===0?totalCohomology:lessons[state.step+1]);if(state.module==='lab')labCompanion();if(state.module==='trace')traceCompanion();if(state.module==='converge')companion(convergence[state.step]);$('.inspector .mini-label').textContent=state.module==='initial'?'图示与记号':state.module==='learn'&&state.step===0?'闭链与边界':'点击图中的项，查看其含义';$('.legend').innerHTML=state.module==='initial'?'<span><i class="h"></i>横向 δ₁</span><span><i class="v"></i>纵向 δ₂</span>'+ (state.step===1?'<span><i class="degree"></i>选中的总次数</span>':''):state.module==='learn'&&state.step===0?'<span><i class="degree"></i>总微分 D</span>':'<span><i class="h"></i>横向 δ₁ / d₁</span><span><i class="v"></i>纵向 δ₂ / d₀</span><span><i class="degree"></i>选中的总次数</span>';$('#panelIndex').textContent=String(state.step+1).padStart(2,'0');renderPersistentDiagram();if(updateControls)controls();inspect();document.querySelectorAll('[data-module]').forEach(b=>b.setAttribute('aria-pressed',b.dataset.module===state.module));const section=state.module==='initial'?'initial':state.module==='converge'?'converge':'induced';document.querySelectorAll('[data-section]').forEach(b=>b.setAttribute('aria-pressed',b.dataset.section===section));$('#submodules').hidden=section!=='induced';renderSlideState();translatePage();window.spectralState={...state,language:language()};}
function move(i){state.cover=false;state.initialReveal=-1;state.annotationStep=1;state.effect=null;state.chosenAction=1;state.seenH=false;state.seenV=false;state.pinned=null;state.pinnedKey=null;state.stackR=null;state.step=Math.max(state.module==='learn'?3:0,Math.min(stepCount()-1,i));if(state.module==='learn'&&state.step===5){state.n=3;state.p=1;state.r=Math.max(1,Math.min(3,state.r));}if(state.module==='lab')state.r=state.step;state.selected=null;render();$('.explanation').scrollTop=0;}
function moduleChange(m){state.cover=false;state.initialReveal=-1;state.annotationStep=1;state.effect=null;state.chosenAction=1;state.seenH=false;state.seenV=false;state.pinned=null;state.pinnedKey=null;state.module=m;state.step=m==='learn'?3:0;state.stackR=null;state.stackStart=0;state.r=0;state.selected=null;if(m==='converge'){state.example='survive';state.n=1;state.p=1;}state.r=m==='lab'?0:m==='converge'?1:2;if(m==='converge'){state.n=3;state.p=1;}location.hash=m;render();$('.explanation').scrollTop=0;}
$('#prev').onclick=()=>{retreatSlide();};$('#next').onclick=()=>{advanceSlide();};
$('#beginSlides').onclick=()=>goSlide(1);$('#coverButton').onclick=()=>{state.module='initial';state.step=0;state.cover=true;state.initialReveal=-1;state.annotationStep=1;state.effect=null;state.chosenAction=1;state.seenH=false;state.seenV=false;state.pinned=null;state.pinnedKey=null;location.hash='title';render();};
document.querySelector('.module-dock').onclick=e=>{let b=e.target.closest('[data-section]');if(b)moduleChange(b.dataset.section==='induced'?'learn':b.dataset.section);};$('#submodules').onclick=e=>{let b=e.target.closest('[data-module]');if(b)moduleChange(b.dataset.module);};$('#stepTrack').onclick=e=>{const b=e.target.closest('[data-slide]');if(b)goSlide(Number(b.dataset.slide));};
$('#viewTabs').onclick=e=>{const b=e.target.closest('[data-view]');if(b)move(Number(b.dataset.view));};
$('#actionTabs').onclick=e=>{const b=e.target.closest('[data-action]');if(b){state.pinned=null;state.pinnedKey=null;state.chosenAction=Number(b.dataset.action);setAnnotation(state.chosenAction);applyConcept(null);}};
$('#controls').addEventListener('input',e=>{let id=e.target.id;if(!id.endsWith('Range'))return;const val=Number(e.target.value);if(id==='nRange'){state.n=val;if(state.module==='converge')state.r=Math.min(state.r,val+2);state.p=Math.min(state.p,val+1);if($('#pRange')){$('#pRange').max=val+1;$('#pRange').value=state.p;$('#pRange').nextElementSibling.textContent=state.p;}}if(id==='pRange')state.p=val;if(id==='lambdaRange')state.lambda=val;if(id==='rRange'){state.r=val;if(state.module==='lab')state.step=val;}e.target.nextElementSibling.textContent=val;state.selected=null;render(id==='nRange'&&state.module==='converge');});
$('#controls').onchange=e=>{if(e.target.id==='exampleSelect'){state.example=e.target.value;state.r=0;state.step=0;state.selected=null;render();}};
$('#controls').onclick=e=>{let b=e.target.closest('[data-direction]');if(b){state.direction=b.dataset.direction;render();}};
function selectNode(e){let b=e.target.closest('[data-p]:not([data-boundary])');if(b){state.selected={p:Number(b.dataset.p),q:Number(b.dataset.q)};render(false);if(['lab','trace'].includes(state.module))$('.inspector').open=true;}}$('#diagram').onclick=selectNode;$('#diagram').onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();const el=e.target.closest('[data-concept]');if(el)pinConcept(el.dataset.concept,interactiveConcept(el));selectNode(e);}};
let fullscreenScroll=0;
function syncFullscreenButton(){const active=document.body.classList.contains('study-fullscreen');$('#fullscreen').textContent=active?'⛶ 退出全屏':'⛶ 全屏';$('#fullscreen').title=active?'退出全屏（Esc）':'全屏显示工作区';$('#fullscreen').setAttribute('aria-pressed',String(active));translatePage();}
function leaveFocusMode(){document.body.classList.remove('study-fullscreen');syncFullscreenButton();window.scrollTo(0,fullscreenScroll);$('#fullscreen').focus({preventScroll:true});}
async function exitStudyFullscreen(){if(document.fullscreenElement){try{await document.exitFullscreen();}catch{}}leaveFocusMode();}
$('#fullscreen').onclick=async()=>{if(document.body.classList.contains('study-fullscreen')){await exitStudyFullscreen();return;}fullscreenScroll=window.scrollY;document.body.classList.add('study-fullscreen');syncFullscreenButton();try{if(document.documentElement.requestFullscreen)await document.documentElement.requestFullscreen();}catch{/* Embedded browsers retain the viewport-filling focus mode. */}};
document.addEventListener('fullscreenchange',()=>{if(!document.fullscreenElement&&document.body.classList.contains('study-fullscreen'))leaveFocusMode();});
document.addEventListener('keydown',e=>{if(e.key==='Escape'&&document.body.classList.contains('study-fullscreen')&&!$('#formulaDialog').open&&!$('#references').open){e.preventDefault();exitStudyFullscreen();}});
$('#proofJump').onclick=()=>{moduleChange('converge');$('.workspace').scrollIntoView({behavior:'smooth'});};
const refHTML=`<p>本主题采用 McCleary《A User’s Guide to Spectral Sequences》第二版的上同调型记号，保留讲义的 K、δ₁、δ₂。滤过固定为按列的下降滤过。</p>${formulas([raw`D=\delta_1+\delta_2,\quad \delta_1\delta_2+\delta_2\delta_1=0`,raw`E_0^{p,q}=\operatorname{Gr}_F^pC^{p+q}\cong K^{p,q}`,raw`E_r^{p,q}=Z_r^{p,q}/(Z_{r-1}^{p+1,q-1}+B_{r-1}^{p,q})`,raw`d_r:E_r^{p,q}\to E_r^{p+r,q-r+1}`,raw`E_\infty^{p,q}\cong\operatorname{Gr}_F^pH^{p+q}`])}<p><b>记号界限：</b>δ₁、δ₂ 是双复形微分；d₀、d₁、… 是页上的微分。Zᵣ、Bᵣ 是总复形中的子空间；[a]ᵣ 是 Eᵣ 的类，[a]H 是总上同调类。动画中示意空间的大小不代表维数。</p><p><b>有限例子：</b>给定全部生成元和箭头，其余项确实为零。基、矩阵与代表元来自精确有理数消元；选择这些基不赋予 H 的滤过一个典范分裂。</p><p><b>阅读依据：</b>Definition 2.2（谱序列）、Definitions 2.3–2.5（滤过与收敛）、Theorem 2.6 及证明（pp. 33–37）、Theorem 2.15（双复形，pp. 48–49）。</p><p><a href="https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/McCleary-UGSS.pdf" target="_blank" rel="noreferrer">打开 McCleary 原书 ↗</a> · <a href="spectral.pdf">打开本主题讲义 ↗</a></p><p>键盘：→、回车和空格前进，← 后退。初始页逐项展开定义，然后切换主线页面。Tab 聚焦，空格固定符号；按钮、选择框和滑块保留自身的键盘行为。</p>`;
$('#referenceContent').innerHTML=refHTML;$('#referenceButton').onclick=()=>{translatePage();$('#references').showModal();};$('#closeReferences').onclick=()=>$('#references').close();
document.addEventListener('keydown',e=>{if(!['Enter','ArrowRight','ArrowLeft'].includes(e.key)||$('#references').open||$('#formulaDialog').open||e.target.closest('input,select,textarea,[contenteditable=true],#pageStack')||e.key==='Enter'&&e.target.closest('button,a'))return;e.preventDefault();e.stopImmediatePropagation();if(e.key==='ArrowLeft')retreatSlide();else advanceSlide();},true);
document.addEventListener('keydown',e=>{if($('#references').open||$('#formulaDialog').open||e.target.closest('[data-formula],.build-card')||e.target.closest('#pageStack')||['INPUT','SELECT','BUTTON','A'].includes(document.activeElement.tagName))return;if(e.key==='ArrowRight')$('#next').click();if(e.key==='ArrowLeft')$('#prev').click();if(e.code==='Space'){e.preventDefault();$('#next').click();}});
window.addEventListener('hashchange',()=>{let m=location.hash.slice(1);if(m==='title'&&!state.cover){$('#coverButton').click();return;}if(['initial','learn','lab','trace','converge'].includes(m)&&(m!==state.module||state.cover))moduleChange(m);});
document.querySelectorAll('[data-tex]').forEach(el=>el.innerHTML=math(el.dataset.tex));
if(['initial','learn','lab','trace','converge'].includes(location.hash.slice(1))){state.module=location.hash.slice(1);state.cover=false;if(state.module==='learn')state.step=3;}
$('#languageButton').onclick=()=>{toggleLanguage();render();};
render();

function openFormula(e){const el=e.target.closest('[data-formula]');if(!el||el.closest('#formulaDialog')||(el.dataset.concept&&!e.target.closest('[data-zoom]')))return;$('#formulaContent').innerHTML=math(el.dataset.formula,true);$('#formulaDialog').showModal();}
document.addEventListener('click',openFormula);
document.addEventListener('keydown',e=>{if((e.key==='Enter'||e.key===' ')&&e.target.matches('[data-formula]')){e.preventDefault();if(e.target.dataset.concept){revealAnnotation(e.target);pinConcept(e.target.dataset.concept,interactiveConcept(e.target));}else openFormula(e);}});
$('#closeFormula').onclick=()=>$('#formulaDialog').close();

function sectionName(){return state.module==='initial'?'01 / INITIAL DATA':state.module==='converge'?'03 / CONVERGENCE':'02 / INDUCED STRUCTURES';}
function statementMeta(){
 const collections={
 initial:[
 {kind:'定义',number:'1.1',name:'双复形',intro:'在上述双分次向量空间上给定以下线性映射，并要求它们满足所列恒等式。',concepts:['delta1','delta2','differential','differential']},
 {kind:'定义',number:'1.2',name:'总复形',intro:'对每个总次数 n，将同一条对角线上的空间取直和，并定义总微分。',concepts:['total','differential','differential']}
 ],
 learn:[
 {kind:'定义',number:'2.1',name:'上同调',concepts:['cycles','boundaries','cohomology','cohomology']},
 {kind:'定义',number:'2.2',name:'列滤过',concepts:['filtration','filtration','differential']},
 {kind:'定义',number:'2.3',name:'关联分次与第零页',concepts:['quotient','quotient','space']},
 {kind:'命题',number:'2.1',name:'第零微分与第一页',concepts:['delta2','cohomology']},
 {kind:'命题',number:'2.2',name:'第一微分与第二页',concepts:['delta1','delta1','quotient']},
 {kind:'定义',number:'2.3',name:'滤过闭链、边界与一般页',concepts:['cycles','boundaries','page','differential','cohomology']}
 ],
 converge:[
 {kind:'定义',number:'3.1',name:'上同调上的诱导滤过',concepts:['cohomology','filtration','quotient']},
 {kind:'引理',number:'3.2',name:'有界性与稳定',intro:'令 n=p+q，并保留第一象限假设。',concepts:['filtration','cycles','boundaries']},
 {kind:'命题',number:'3.3',name:'典范比较映射',concepts:['page','comparison','comparison']},
 {kind:'定理',number:'3.4',name:'有界滤过的收敛',concepts:['filtration','cycles','comparison','boundaries','comparison']},
 {kind:'解释与结论',number:'3.5',name:'收敛的意义',concepts:['comparison','filtration']}
 ]};
 return collections[state.module]?.[state.step]||{kind:state.module==='lab'?'例':'计算',number:`2.${state.module==='lab'?'7':'8'}.${state.step+1}`,concepts:state.module==='lab'?['page','differential']:['differential','space','differential']};
}
function arrowConcept(type){return type==='h'?'delta1':type==='v'?'delta2':'differential';}
function renderSlideState(){
 const deck=$('.slide-deck'),cover=state.cover;deck.dataset.module=state.module;
 deck.classList.toggle('is-building',isDoubleComplexView());deck.classList.toggle('is-cover',cover);deck.classList.toggle('has-diagram',!cover);deck.classList.toggle('has-explanation',!cover);
 $('#slideCover').hidden=!cover;$('.slide-body').inert=cover;$('#visualPanel').inert=cover;
 if(cover){$('#sceneKicker').textContent='STUDY ATLAS / AT·002';$('#sceneTitle').textContent='';}
 const page=mainSlide();
 $('#stepReadout').textContent=`${String(page+1).padStart(2,'0')} / 04`;
 $('#prev').disabled=cover;$('#next').disabled=page===3;
 $('#prev').textContent=ui('← 上一页','← Previous');$('#next').textContent=ui('下一页 →','Next →');
 $('#fragmentTrack').textContent=state.module==='initial'?'':ui('主线翻页 · 图内操作不占页数','Main slides · interactions stay on this slide');
 $('#stepTrack').innerHTML=[ui('标题','Title'),'Initial data','Induced structures','Convergence'].map((t,i)=>`<button data-slide="${i}" class="${page===i?'active':''}" aria-label="${t}" title="${t}"></button>`).join('');
 $('#viewTabs').innerHTML=viewNames(state,language()).map((t,i)=>`<button data-view="${state.module==='learn'?i+3:i}" aria-pressed="${state.step===(state.module==='learn'?i+3:i)}">${t}</button>`).join('');
 if($('#diagram .continuation'))$('.legend').insertAdjacentHTML('beforeend','<span><i class="continuation-key"></i>虚线：中间项省略</span>');
 $('#sceneNote').hidden=cover;updateDiagramScope();
 renderQuickCheck();if(isDoubleComplexView())setupDoubleComplex();else updateAnnotations();applyConcept(state.pinned,false);
}
function ui(zh,en){return language()==='en'?en:zh;}
function mainSlide(){return state.cover?0:state.module==='initial'?1:state.module==='converge'?3:2;}
function goSlide(i){if(i===0){$('#coverButton').click();return;}moduleChange(['','initial','learn','converge'][Math.max(1,Math.min(3,i))]);}
function advanceSlide(){if(isDoubleComplexView()&&state.initialReveal<INITIAL_STEPS){advanceInitial(1);return;}if(mainSlide()<3)goSlide(mainSlide()+1);}
function retreatSlide(){if(isDoubleComplexView()&&state.initialReveal>=0){advanceInitial(-1);return;}if(mainSlide()>0)goSlide(mainSlide()-1);}
function initialConcept(){return ['space','delta1','delta2','square1','anticommute','total','totalmap','filtration','zeropage'][state.initialReveal];}
function advanceInitial(direction){
 state.initialReveal=Math.max(-1,Math.min(INITIAL_STEPS,state.initialReveal+direction));state.seenH=state.initialReveal>=1;state.seenV=state.initialReveal>=2;state.effect=initialConcept();state.pinned=null;state.pinnedKey=null;render();
 keepDefinitionVisible();
}
function keepDefinitionVisible(){
 cancelAnimationFrame(definitionScrollFrame);
 const pane=$('.explanation'),card=$(`[data-build="${state.initialReveal}"]`),until=performance.now()+(matchMedia('(prefers-reduced-motion:reduce)').matches?0:450);
 if(!card){pane.scrollTop=0;return;}
 const follow=()=>{if(!card.isConnected||!isDoubleComplexView())return;const r=card.getBoundingClientRect(),b=pane.getBoundingClientRect();if(r.bottom>b.bottom)pane.scrollTop+=r.bottom-b.bottom+12;else if(r.top<b.top)pane.scrollTop-=b.top-r.top+12;if(performance.now()<until)definitionScrollFrame=requestAnimationFrame(follow);};follow();
}

function interactiveConcept(target){
 if(!(target instanceof Element))return null;
 if(target.closest('[data-zoom]'))return null;
 return target.closest('.relation-choice')||target.closest('.build-card')||target.closest('.formal-statement > .math-block[data-concept]')||target.closest('#diagram [data-concept]');
}
function interactionKey(el){
 if(!el)return null;
 if(el.matches('.relation-choice'))return `relation:${el.dataset.concept}`;
 if(el.matches('.build-card'))return `build:${el.dataset.build}`;
 if(el.matches('.formal-statement > .math-block'))return `formula:${[...el.parentElement.querySelectorAll(':scope > .math-block')].indexOf(el)}`;
 if(el.matches('.node'))return `node:${el.dataset.p}:${el.dataset.q}`;
 return `diagram:${el.dataset.concept}`;
}
function applyConcept(concept,hover=false,source=null){
 if(isDoubleComplexView()&&!concept)concept=initialConcept();
 const key=source?interactionKey(source):state.pinnedKey||(isDoubleComplexView()&&state.initialReveal?`build:${state.initialReveal}`:null);
 if(isDoubleComplexView()&&state.effect!==concept){state.effect=concept;renderPersistentDiagram();}
 const graph=$('#diagram');
 graph.querySelectorAll('.concept-active').forEach(el=>el.classList.remove('concept-active'));
 graph.classList.toggle('concept-focus',!!concept);graph.classList.toggle('hover-effect',!!concept&&hover);
 const targets={square1:'.relation-route',square2:'.relation-route',anticommute:'.relation-route',delta1:'.arrow.h,.continuation[data-concept=delta1]',delta2:'.arrow.v,.continuation[data-concept=delta2]',differential:'.arrow,.continuation[data-concept=delta1],.continuation[data-concept=delta2],.continuation[data-concept=differential]',space:'.node:not(.outside-quadrant) .node-bg',page:'.node:not(.outside-quadrant) .node-bg',quotient:'.node:not(.muted):not(.outside-quadrant) .node-bg',totalmap:'.diag-box,.diag,#diagram-edges>g:not(.context-edge) .arrow,#diagram-edges>g:not(.context-edge) .continuation',total:'.diag-box,.diag,.node:not(.muted):not(.outside-quadrant) .node-bg,.continuation[data-concept=total]',zeropage:'.node:not(.muted):not(.outside-quadrant) .node-bg',filtration:'.diag-box,.node:not(.muted):not(.outside-quadrant) .node-bg',cycles:'[data-concept=cycles]',boundaries:'[data-concept=boundaries]',cohomology:'.node:not(.muted):not(.outside-quadrant) .node-bg',comparison:'.node:not(.zero) .node-bg,.diag-box'};
 if(concept){
  const nodeKey=key?.startsWith('node:')?key.split(':'):null;
  const selector=nodeKey?`.node[data-p="${nodeKey[1]}"][data-q="${nodeKey[2]}"] .node-bg`:targets[concept];
  if(selector)graph.querySelectorAll(selector).forEach(el=>el.classList.add('concept-active'));
 }
 graph.querySelectorAll('.map-label').forEach(el=>el.classList.toggle('map-active',!concept||el.dataset.mapConcept===concept||['totalmap','differential'].includes(concept)));
 // Left-hand emphasis belongs to one source item, never to a concept family.
 document.querySelectorAll('.formal-statement .concept-linked').forEach(el=>el.classList.remove('concept-linked'));
 document.querySelectorAll('.formal-statement [aria-pressed]').forEach(el=>el.setAttribute('aria-pressed','false'));
 document.querySelectorAll('.formal-statement .build-card,.formal-statement > .math-block').forEach(el=>{
  const ownKey=interactionKey(el);el.classList.toggle('concept-linked',!!concept&&(ownKey===key||el.dataset.build==='3'&&key?.startsWith('relation:')));
  el.setAttribute('aria-pressed',String(!!state.pinned&&ownKey===state.pinnedKey));
 });
 $('#clearConcept').hidden=!state.pinned;renderOperation();window.spectralState={...state,language:language()};
}
function pinConcept(concept,source=null){
 const key=interactionKey(source);const same=state.pinned===concept&&state.pinnedKey===key;
 state.pinned=same?null:concept;state.pinnedKey=same?null:key;
 applyConcept(state.pinned,false);translatePage();window.spectralState={...state,language:language()};
}
function enterConcept(el){revealDirections(el);revealAnnotation(el);applyConcept(el.dataset.concept,true,el);}
document.addEventListener('pointerover',e=>{const el=interactiveConcept(e.target);if(el&&interactiveConcept(e.relatedTarget)!==el)enterConcept(el);});
document.addEventListener('pointerout',e=>{const el=interactiveConcept(e.target);if(el&&interactiveConcept(e.relatedTarget)!==el)restoreInteraction();});
document.addEventListener('focusin',e=>{const el=interactiveConcept(e.target);if(el)enterConcept(el);});
document.addEventListener('focusout',e=>{const el=interactiveConcept(e.target);if(el&&interactiveConcept(e.relatedTarget)!==el)restoreInteraction();});
document.addEventListener('click',e=>{const el=interactiveConcept(e.target);if(el){revealDirections(el);revealAnnotation(el);pinConcept(el.dataset.concept,el);}});
$('#clearConcept').onclick=()=>{state.pinned=null;state.pinnedKey=null;restoreInteraction();};
function restoreInteraction(){if(!isDoubleComplexView()){const i=state.pinnedKey?.startsWith('formula:')?Number(state.pinnedKey.split(':')[1])+1:state.chosenAction||1;setAnnotation(i);}applyConcept(state.pinned,false);}

function renderQuickCheck(){
 const checks={initial:['如果先作用 δ₂，再作用 δ₁，终点在哪里？','终点是 Kᵖ⁺¹ᑫ⁺¹。交换作用顺序仍到同一位置，但两条复合映射之和为零。'],learn:['dᵣ 的靶在哪里？总次数改变多少？','靶是 Eᵣᵖ⁺ʳ,ᑫ⁻ʳ⁺¹，因此总次数从 p+q 变成 p+q+1。'],converge:['稳定页是否给出了 Hⁿ 的典范直和分解？','没有。它典范地给出滤过商 GrᵖHⁿ。向量空间层面的分裂可以选择，但收敛本身不指定典范分裂。']};
 const entry=state.module==='initial'?null:checks[state.module],el=$('#quickCheck');el.hidden=!entry||state.cover||state.step!==stepCount()-1;
 el.innerHTML=entry?`<summary><span>自检</span> · <span>${entry[0]}</span></summary><p>${entry[1]}</p>`:'';
}

function continuation(x1,y1,x2,y2,concept=''){const marker=concept==='delta1'?'h':concept==='delta2'?'v':concept==='total'||concept==='differential'?'r':'continuation';return `<path class="continuation" ${concept?`data-concept="${concept}" tabindex="0"`:''} d="M${x1},${y1} L${x2},${y2}" marker-end="url(#arrow-${marker})" role="${concept?'button':'img'}" aria-label="延续箭头：省略中间项，不表示一次微分"><title>延续箭头：省略中间项，不表示一次微分</title></path>`;}

function isDoubleComplexView(){return !state.cover&&state.module==='initial'&&state.step===0;}
function doubleComplexCompanion(item){
 $('#sceneKicker').textContent=sectionName();$('#sceneTitle').textContent='Initial data';
 if($('.build-statement')?.dataset.contentLanguage===language())return;
 const cards=[
 {title:'横向微分 δ₁',concept:'delta1',f:[item.f[0]]},
 {title:'纵向微分 δ₂',concept:'delta2',f:[item.f[1]]},
 {title:'平方零关系',concept:'square1',f:[]},
 {title:'反交换关系',concept:'anticommute',f:[item.f[3]]},
 {title:'总复形',concept:'total',f:[raw`C^\bullet:=\operatorname{Tot}^\bullet K`,raw`C^n:=\bigoplus_{p+q=n}K^{p,q}`]},
 {title:'总微分',concept:'totalmap',f:[raw`D:=\delta_1+\delta_2`,raw`D:C^n\longrightarrow C^{n+1},\qquad D^2=0`]},
 {title:'列滤过',concept:'filtration',f:[raw`F^pC^n:=\bigoplus_{i\ge p}K^{i,n-i}`,raw`D(F^pC^n)\subseteq F^pC^{n+1}`]},
 {title:'关联分次与第零页',concept:'zeropage',f:[raw`E_0^{p,q}:=\frac{F^pC^{p+q}}{F^{p+1}C^{p+q}}\cong K^{p,q}`]}
 ];
 const assumptions=[raw`K=\{K^{p,q}\}_{(p,q)\in\mathbb Z^2}`,raw`K^{p,q}=0\qquad(p<0\ \text{or}\ q<0)`];
 $('#explanation').innerHTML=`<article class="formal-statement build-statement" data-content-language="${language()}"><div class="statement-heading"><span>定义</span><span class="statement-number">1.1</span></div><div class="initial-definition" data-build="0"><h3>双复形</h3><div class="initial-assumptions">${assumptions.map(f=>`<div>${math(f,true)}</div>`).join('')}</div></div><p class="coordinate-prelude-title">坐标图</p>${cards.map((c,i)=>`<section class="build-card" data-build="${i+1}" data-concept="${c.concept}" tabindex="0" role="button"><h4><span class="build-number">${String(i+1).padStart(2,'0')}</span><span>${c.title}</span></h4>${c.f.map(f=>block(f,c.concept)).join('')}${i===2?`<div class="relation-choices"><button class="relation-choice" data-concept="square1">${math(raw`\delta_1^2=0`)}</button><button class="relation-choice" data-concept="square2">${math(raw`\delta_2^2=0`)}</button></div>`:''}</section>`).join('')}</article>`;
 $('#sceneNote').textContent='';
}
function setupDoubleComplex(){
 document.querySelectorAll('.build-card').forEach(el=>{const visible=Number(el.dataset.build)<=state.initialReveal,appearing=el.hidden&&visible;el.hidden=!visible;el.classList.toggle('is-available',visible);el.inert=!visible;if(appearing)void el.offsetWidth;el.classList.toggle('build-current',visible&&Number(el.dataset.build)===state.initialReveal);el.classList.toggle('build-complete',visible&&Number(el.dataset.build)<state.initialReveal);});
 $('.build-statement').classList.toggle('is-coordinate-prelude',state.initialReveal<0);$('.initial-definition').hidden=state.initialReveal<0;if(state.initialReveal===0)void $('.initial-definition').offsetWidth;$('.initial-definition').classList.toggle('definition-current',state.initialReveal===0);
 $('#actionTabs').innerHTML='';$('#sceneNote').textContent='';$('#sceneNote').hidden=true;
 $('#next').textContent=state.initialReveal<INITIAL_STEPS?ui('下一步 →','Next step →'):ui('下一页 →','Next slide →');$('#prev').textContent=state.initialReveal>=0?ui('← 上一步','← Previous step'):ui('← 上一页','← Previous slide');
 $('#fragmentTrack').innerHTML=math(state.initialReveal<0?raw`(p,q)`:[raw`K^{p,q}`,raw`\delta_1`,raw`\delta_2`,raw`\delta_1^2=\delta_2^2=0`,raw`\delta_1\delta_2+\delta_2\delta_1=0`,raw`C^\bullet`,raw`D`,raw`F^pC^n`,raw`E_0^{p,q}`][state.initialReveal]);
 $('#next').setAttribute('aria-label',$('#next').textContent);$('#prev').setAttribute('aria-label',$('#prev').textContent);
 $('#controls').inert=state.initialReveal<5;$('#controls').style.visibility=state.initialReveal<5?'hidden':'visible';
}
function revealDirections(el){
 if(!isDoubleComplexView())return;
 const concept=el.dataset.concept;
 if(['delta1','square1','anticommute','totalmap'].includes(concept))state.seenH=true;
 if(['delta2','square2','anticommute','totalmap'].includes(concept))state.seenV=true;
 renderPersistentDiagram();
}
document.addEventListener('keydown',e=>{if((e.key==='Enter'||e.key===' ')&&e.target.matches('.build-card')){e.preventDefault();revealDirections(e.target);pinConcept(e.target.dataset.concept,interactiveConcept(e.target));}});
function renderOperation(){
 $('#operationBoard').innerHTML=state.module==='initial'&&state.initialReveal<0?`<div class="operation-equation">${math(raw`(p,q)\in\mathbb Z^2`)}</div>`:operationMarkup(state,language(),math);
 syncPageStack();emphasizeCurrentDefinition();
}

// The coordinate frame is mounted once. Only keyed mathematical layers change.
function fixedDiagram(){
 const n=state.n,p=state.p,a=state.annotationStep||0,m=state.module,s=state.step;
 let base=svgStart(GRID_MAX,GRID_MAX),end=base.indexOf('</defs>')+7;
 let frame=base.slice(end),edges='',terms='',overlay='',caption='',kind='K',h=false,v=false,filter=false,total=false,selected=false;
 const finite=['lab','trace'].includes(m);
 if(m==='initial'){
  total=['total','totalmap','filtration'].includes(state.effect);filter=state.effect==='filtration';h=total?state.effect==='totalmap':state.seenH;v=total?state.effect==='totalmap':state.seenV;
  if(state.effect==='zeropage'){kind='E_0';h=false;v=false;selected=true;}
  if(s===0)overlay+=relationOverlay(state.effect);
  if(total)caption=raw`C^{${n}}=\bigoplus_{i=0}^{${n}}K^{i,${n}-i}`;
 }else if(m==='learn'){
  if(s<=2){h=s===0||s===1&&a===3;v=h;total=a>0;filter=s>=1;selected=s===2&&a>=2;if(s===2&&a>=3){h=false;v=false;}}
  if(s===0)caption=a===1?raw`Z^{${n}}=\ker(D:C^{${n}}\to C^{${n+1}})`:a===2?raw`B^{${n}}=\operatorname{im}(D:C^{${n-1}}\to C^{${n}})`:raw`H^{${n}}=Z^{${n}}/B^{${n}}`;
  if(s===1&&a>0)caption=raw`F^{${p}}C^{${n}}=\bigoplus_{i=${p}}^{${n}}K^{i,${n}-i}`;
  if(s===2&&a>0)caption=raw`E_0^{${p},${n-p}}\cong K^{${p},${n-p}}`;
  if(s===3){kind=a>=2?'E_1':'E_0';v=a===1;caption=a>=2?raw`E_1^{i,j}=H^j(K^{i,\bullet},\delta_2)`:raw`d_0[a]=[Da]=[\delta_2a]`;}
  if(s===4){kind=a>=3?'E_2':'E_1';h=a>=1&&a<3;caption=a>=3?raw`E_2^{i,j}=H^i(E_1^{\bullet,j},d_1)`:raw`d_1[a]=[\delta_1a]`;}
  if(s===5){const r=Math.max(1,state.r);kind=a===5?`E_${r+1}`:a>=3?`E_${r}`:'K';if(a===4)edges+=line(...xy(1,2),...xy(1+r,3-r),'r',true,`d_${r}`);if(a<=2){total=true;filter=true;}caption=a<=2?raw`Z_r^{p,q},B_r^{p,q}\subseteq C^{p+q}`:raw`d_r:E_r^{p,q}\to E_r^{p+r,q-r+1}`;}
 }
 if(m==='converge'){
  kind=s>=2?'E_\\infty':'K';total=s<2;filter=s<2;
  if(s>=2)caption=raw`E_\infty^{${p},${n-p}}\cong F^{${p}}H^{${n}}/F^{${p+1}}H^{${n}}`;
  if(s===1)caption=raw`p+r>${n+1}\;\Longrightarrow\;F^{p+r}C^{${n+1}}=0`;
 }
 if(total){overlay+=diagonal(n,filter?p:0,true,false);overlay+=`<g class="source-label">${label(500,16,filter?raw`F^{${p}}C^{${n}}`:raw`C^{${n}}`,130,26,true)}</g>`;}
 if(m==='learn'&&s===2&&a>=2)overlay+=`<g class="denominator-region">${diagonal(n,p+1,true,false)}</g>`;
 const showNext=(m==='initial'&&state.effect==='totalmap')||(m==='learn'&&s===0&&a===1)||(m==='learn'&&s===1&&a>=3);
 if(showNext)overlay+=`<g class="next-total">${diagonal(n+1,filter?p:0,true,false)}</g>`;
 if(m==='learn'&&s===0&&a===2&&n>0)overlay+=`<g class="next-total">${diagonal(n-1,0,true,false)}</g>`;
 if(m==='learn'&&s===5&&a<=2){const degree=a===1?n+1:n-1,column=a===1?p+Math.max(1,state.r):p-Math.max(1,state.r);if(degree>=0)overlay+=`<g class="next-total">${diagonal(degree,column,true,false)}</g>`;overlay+=`<g class="target-label">${label(650,16,raw`F^{${column}}C^{${degree}}${degree<0||column>degree?'=0':''}`,150,26,true)}</g>`;}
 if(m==='converge'&&s===1){overlay+=`<g class="next-total">${diagonal(n+1,p+Math.max(1,state.r),true,false)}</g>`;overlay+=`<g class="target-label">${label(650,16,raw`F^{${p+Math.max(1,state.r)}}C^{${n+1}}${p+Math.max(1,state.r)>n+1?'=0':''}`,150,26,true)}</g>`;}
 if(showNext)overlay+=`<g class="target-label">${label(650,16,filter?raw`F^{${p}}C^{${n+1}}`:raw`C^{${n+1}}`,130,26,true)}</g>`;
 if(!finite){
  for(let i=0;i<=GRID_MAX;i++)for(let j=0;j<=GRID_MAX;j++){
   let activeSource=!total||i+j===(m==='learn'&&s===0&&a===2?n-1:n)&&(!filter||i>=p);
   if(h&&i<GRID_MAX)edges+=`<g class="${activeSource?'':'context-edge'}">${line(...xy(i,j),...xy(i+1,j),'h',true,m==='initial'||j===2&&i===1?(kind==='E_1'?'d_1':'\\delta_1'):'')}</g>`;
   if(v&&j<GRID_MAX)edges+=`<g class="${activeSource?'':'context-edge'}">${line(...xy(i,j),...xy(i,j+1),'v',true,m==='initial'||i===1&&j===2?(kind==='E_0'?'d_0':'\\delta_2'):'')}</g>`;
   let muted=selected?!(i===p&&i+j===n):total&&(!((i+j===n||showNext&&i+j===n+1)&&(!filter||i>=p)));
   if(m==='learn'&&s===0&&a===2&&i+j===n-1)muted=false;
   if(m==='converge'&&s>=2)muted=!(i===p&&i+j===n);
   terms+=node(i,j,`${kind}^{${i},${j}}`,{muted});
  }
  // Edge-of-window continuations have the same reveal and color rules as their direction.
  for(let k=0;k<=GRID_MAX;k++){
   if(h)edges+=`<g class="${total&&GRID_MAX+k!==n?'context-edge':''}">${continuation(787,xy(0,k)[1],813,xy(0,k)[1],'delta1')}</g>`;
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
function syncGraphChildren(target,source){
 if(target.innerHTML===source.innerHTML)return;
 if(target.id==='diagram-terms'){
  for(const next of [...source.children]){
   const old=target.querySelector(`[data-p="${next.dataset.p}"][data-q="${next.dataset.q}"]`);
   if(!old){target.append(next);continue;}
   for(const attr of [...old.attributes])if(!next.hasAttribute(attr.name))old.removeAttribute(attr.name);
   for(const attr of [...next.attributes])old.setAttribute(attr.name,attr.value);
   if(old.querySelector('.math-anchor')?.dataset.tex!==next.querySelector('.math-anchor')?.dataset.tex){
    const label=next.querySelector('.math-anchor');old.querySelector('.math-anchor').replaceWith(label);fadeGraphAddition(label);
   }
  }
 }else{
  const key=el=>{const shape=el.matches('path,polygon,rect,foreignObject')?el:el.querySelector('path,polygon,rect,foreignObject');return el.tagName+':'+(shape?[shape.tagName,shape.getAttribute('d'),shape.getAttribute('points'),shape.getAttribute('x'),shape.getAttribute('y')].join(':'):el.outerHTML);};
  const existing=new Map([...target.children].map(el=>[key(el),el]));let cursor=target.firstElementChild;
  for(const next of [...source.children]){
   const k=key(next),old=existing.get(k);let el=old||next;
   if(old){existing.delete(k);if(old.outerHTML!==next.outerHTML){for(const attr of [...old.attributes])if(!next.hasAttribute(attr.name))old.removeAttribute(attr.name);for(const attr of [...next.attributes])old.setAttribute(attr.name,attr.value);old.innerHTML=next.innerHTML;}}
   if(el!==cursor)target.insertBefore(el,cursor);cursor=el.nextElementSibling;
   if(!old)fadeGraphAddition(el);
  }
  for(const el of existing.values())el.remove();
 }
}
function fadeGraphAddition(el){if(!matchMedia('(prefers-reduced-motion: reduce)').matches)el.animate([{opacity:0},{opacity:1}],{duration:280});}
function annotationCount(){return document.querySelectorAll('.formal-statement > .math-block').length;}
function updateAnnotations(){
 if(state.cover||isDoubleComplexView())return;
 const a=state.annotationStep||1;
 $('#actionTabs').innerHTML=actionNames(state,language()).map((name,i)=>`<button data-action="${i+1}" aria-pressed="${a===i+1}">${name}</button>`).join('');
 document.querySelectorAll('.formal-statement > .math-block').forEach((el,i)=>{el.dataset.annotation=String(i+1);el.classList.toggle('annotation-seen',i+1===a);el.classList.toggle('definition-current',i+1===(state.chosenAction||1));});
 renderQuickCheck();window.spectralState={...state,language:language()};renderOperation();
}
function setAnnotation(i){state.stackR=null;state.annotationStep=Math.max(1,Math.min(annotationCount(),i));renderPersistentDiagram();updateAnnotations();translatePage();}
function revealAnnotation(el){if(state.cover||isDoubleComplexView())return;const formula=el.closest('.formal-statement > .math-block');if(formula)setAnnotation(Number(formula.dataset.annotation));}

function updateDiagramScope(){
 let el=$('.diagram-scope');if(!el){el=document.createElement('p');el.className='diagram-scope';$('#stage .legend').before(el);}
 if(state.module==='initial'){el.innerHTML=math(raw`0\le p,q\le4`);el.title=ui('坐标窗口；窗口以外不自动为零。','Coordinate window; terms outside are not assumed zero.');return;}el.removeAttribute('title');
 el.textContent=['lab','trace'].includes(state.module)?'有限例子：图中节点显示所选页的向量空间；未列出的生成元为零。':'坐标窗口：0 至 4；右端和上端仍可延伸。';if(state.n===4&&((state.module==='initial'&&state.step===1)||(state.module==='learn'&&state.step<=1)))el.textContent=ui('窗口为 0–4；C⁵ 的 (0,5)、(5,0) 分量在窗口外，仍须计入直和。','Window: 0–4. The (0,5) and (5,0) factors of C⁵ lie outside it and still belong to the direct sum.');
}

// Keep HTML math out of SVG foreignObject: WebKit must scale the whole label plane once.
function syncDiagramLabels(){
 const host=$('#diagram');let plane=host.querySelector('.diagram-label-plane');
 if(!plane){plane=document.createElement('div');plane.className='diagram-label-plane';plane.setAttribute('aria-hidden','true');host.append(plane);}
 const old=new Map([...plane.children].map(el=>[el.dataset.key,el]));
 for(const anchor of host.querySelectorAll('svg .math-anchor')){
  const d=anchor.dataset,key=[d.x,d.y,d.width,d.height].join(':'),el=old.get(key)||document.createElement('div');old.delete(key);
  el.className='diagram-label'+(anchor.closest('.node')?' term-label':'')+(d.small==='true'?' small-label':'')+(anchor.closest('.diagram-caption')?' caption-label':'')+(anchor.closest('.source-label')?' source-label':'')+(anchor.closest('.target-label')?' target-label':'');el.dataset.key=key;
  const map=anchor.previousElementSibling?.matches('.arrow')?anchor.previousElementSibling:null;if(map){el.classList.add('map-label',map.classList.contains('h')?'map-h':map.classList.contains('v')?'map-v':'map-r');el.dataset.mapConcept=map.dataset.concept;}else delete el.dataset.mapConcept;
  el.style.left=d.x+'px';el.style.top=d.y+'px';el.style.width=d.width+'px';el.style.height=d.height+'px';
  el.style.opacity=(anchor.closest('.muted') ? .22 : 1)*(anchor.closest('.zero') ? .38 : 1)*(anchor.closest('.context-edge') ? .2 : 1);
  const changed=el.dataset.tex!==d.tex;if(changed){el.innerHTML=math(d.tex);el.dataset.tex=d.tex;}
  if(!el.isConnected)plane.append(el);if(changed)fadeGraphAddition(el);
 }
 for(const el of old.values())el.remove();
}
function observeDiagramSize(){
 const viewport=$('.diagram-viewport'),host=$('#diagram');
 const fit=()=>{const rect=viewport.getBoundingClientRect(),width=Math.max(0,Math.min(rect.width,rect.height*840/525));host.style.width=width+'px';host.style.height=width*525/840+'px';host.style.setProperty('--diagram-scale',String(width/840));};
 diagramResizeObserver=new ResizeObserver(fit);diagramResizeObserver.observe(viewport);fit();
}

function relationOverlay(effect){
 if(!['square1','square2','anticommute'].includes(effect))return '';
 const edge=(p,q,p1,q1,type,order)=>`<g class="relation-route route-${order}">${line(...xy(p,q),...xy(p1,q1),type,true)}</g>`;
 let out='';
 if(effect==='square1'||effect==='square2'){
  const horizontal=effect==='square1',end=horizontal?[3,1]:[1,3];
  out+=edge(1,1,horizontal?2:1,horizontal?1:2,horizontal?'h':'v',1);
  out+=edge(horizontal?2:1,horizontal?1:2,...end,horizontal?'h':'v',2);
  const [x,y]=xy(...end);out+=`<g class="relation-result"><rect x="${x+35}" y="${y-37}" width="31" height="24" rx="12" fill="#263e35" stroke="#f4c876"/>${label(x+50,y-25,'0',24,22,true)}</g>`;
 }else{
  out+=edge(1,1,2,1,'h',1)+edge(2,1,2,2,'v',2)+edge(1,1,1,2,'v',1)+edge(1,2,2,2,'h',2);
 }
 return `<g class="relation-overlay">${out}</g>`;
}

function defaultStackPage(){
 if(state.module==='learn')return state.step===3?(state.annotationStep>=2?1:0):state.step===4?(state.annotationStep>=3?2:1):Math.max(1,state.r)+(state.annotationStep===5?1:0);
 return Math.max(1,state.r);
}
function syncPageStack(){
 const enabled=['learn','converge'].includes(state.module)&&!state.cover;
 let toolbar=$('#diagramViews'),stack=$('#pageStack');
 if(!toolbar){
  toolbar=document.createElement('nav');toolbar.id='diagramViews';toolbar.className='diagram-views';$('#stage').prepend(toolbar);
  stack=document.createElement('div');stack.id='pageStack';$('.diagram-viewport').append(stack);
  toolbar.addEventListener('change',e=>{if(e.target.id==='stackPageSelect'){state.stackR=Number(e.target.value);syncPageStack();}});
  toolbar.addEventListener('click',e=>{
   const mode=e.target.closest('[data-diagram-mode]'),shift=e.target.closest('[data-page-window]');
   if(mode)state.diagramMode=mode.dataset.diagramMode;
   if(shift){state.stackStart=Math.max(0,state.stackStart+Number(shift.dataset.pageWindow)*(matchMedia('(max-width:780px)').matches?2:4));state.stackR=state.stackStart;}
   renderOperation();
  });
  const select=e=>{const target=e.target.closest('[data-stack-r]');if(!target)return;state.stackR=Number(target.dataset.stackR);if(target.dataset.stackP)state.stackPoint={p:Number(target.dataset.stackP),q:Number(target.dataset.stackQ)};syncPageStack();};
  stack.addEventListener('click',select);
  stack.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();e.stopPropagation();select(e);}});
 }
 toolbar.hidden=!enabled;stack.hidden=!enabled||state.diagramMode!=='3d';$('#diagram').hidden=enabled&&state.diagramMode==='3d';
 $('#stage').classList.toggle('has-page-stack',enabled&&state.diagramMode==='3d');
 if(!enabled){$('.legend').hidden=false;$('#pageRelation')?.setAttribute('hidden','');return;}
 const current=state.stackR??defaultStackPage(),point=state.stackPoint||{p:1,q:2},compact=matchMedia('(max-width:780px)').matches,count=compact?2:4;
 state.stackStart=Math.floor(current/count)*count;
 toolbar.innerHTML=`<div class="diagram-modes"><button data-diagram-mode="3d" aria-pressed="${state.diagramMode==='3d'}">${ui('3D · 多页','3D · Pages')}</button><button data-diagram-mode="2d" aria-pressed="${state.diagramMode==='2d'}">${ui('2D · 定义图','2D · Definition')}</button></div><div class="page-window" ${state.diagramMode==='2d'?'hidden':''}><button data-page-window="-1" aria-label="${ui('更早的页','Earlier pages')}" ${state.stackStart===0?'disabled':''}>−</button><label class="stack-page-select">r <select id="stackPageSelect" aria-label="${ui('选择谱序列页','Select spectral-sequence page')}">${Array.from({length:count},(_,i)=>state.stackStart+i).map(r=>`<option value="${r}" ${r===current?'selected':''}>${r}</option>`).join('')}</select></label><span class="stack-window-label">${state.stackStart}–${state.stackStart+count-1}</span><button data-page-window="1" aria-label="${ui('后续各页','Later pages')}">+</button></div>`;
 const model=pageStackMarkup({start:state.stackStart,current,...point,lang:language(),compact},math);
 const key=[state.stackStart,current,point.p,point.q,language(),compact].join(':');
 if(stack.dataset.key!==key){stack.innerHTML=model.svg;stack.dataset.key=key;}
 if(state.diagramMode==='3d'){
  stack.querySelector('svg').setAttribute('viewBox',compact?'0 0 470 300':'0 0 840 525');
  $('.legend').hidden=true;
  const scope=$('.diagram-scope');if(scope){scope.innerHTML=model.formula;scope.title=model.note;}
  let relation=$('#pageRelation');if(!relation){relation=document.createElement('div');relation.id='pageRelation';$('#stage').append(relation);}
  relation.innerHTML=`<span>${model.relation}</span><small>${ui('同调关系 · 非层间箭头','Cohomology relation · no inter-page arrow')}</small>`;relation.hidden=false;
  if(state.stackR!==null){
   const next=current+1;
   $('#operationBoard').innerHTML=`<div class="operation-content"><div class="operation-equation">${model.formula}</div><div class="operation-equation">${math(raw`E_{${next}}\cong H(E_{${current}},d_{${current}})`)}</div></div><p class="operation-note">${model.note}</p>`;
  }
 }else{$('.legend').hidden=false;$('#pageRelation')?.setAttribute('hidden','');updateDiagramScope();}
 window.spectralState={...state,stackCurrent:current,language:language()};
}

// Reveal the page only after first render and all bundled math fonts are ready.
(async()=>{
 window.spectralBoot?.progress(65,'排版数学公式','Typesetting mathematics');
 const fonts=[...document.fonts].filter(f=>f.family.includes('KaTeX'));
 const loaded=await Promise.allSettled(fonts.map(f=>f.load()));
 if(loaded.some(f=>f.status==='rejected')){window.spectralBoot?.fail();return;}
 await document.fonts.ready;
 window.spectralBoot?.progress(100,'准备就绪','Ready');
 requestAnimationFrame(()=>requestAnimationFrame(()=>window.spectralBoot?.ready()));
})().catch(()=>window.spectralBoot?.fail());

matchMedia('(max-width:780px)').addEventListener('change',()=>syncPageStack());

function syncCoordinatePresentation(){
 const graph=$('#diagram'),frameOnly=state.module==='initial'&&state.initialReveal<0;
 const symbolic=['initial','learn','converge'].includes(state.module)&&!frameOnly;
 graph.classList.toggle('frame-only',frameOnly);graph.classList.toggle('symbolic-coordinates',symbolic);
 graph.querySelectorAll('.axis-tick').forEach(tick=>{
  const v=Number(tick.dataset.value),horizontal=tick.dataset.axis==='p',close=frameOnly&&v>=0;
  if(horizontal){tick.setAttribute('x',xy(v,0)[0]-(close&&v===0?10:0));tick.setAttribute('y',xy(0,0)[1]+(close?20:38));}
  else{tick.setAttribute('x',xy(0,0)[0]-(close?12:56));tick.setAttribute('y',xy(0,v)[1]+5);}
  tick.setAttribute('aria-hidden',String(symbolic&&v>=0));tick.classList.toggle('redundant-coordinate',symbolic&&v>=0);
 });
 graph.querySelector('#diagram-terms').setAttribute('aria-hidden',String(frameOnly));
 graph.querySelectorAll('.node:not(.outside-quadrant)').forEach(node=>node.setAttribute('tabindex',frameOnly?'-1':'0'));
}

// One finite emphasis per definition stage. Geometry and the right pane stay fixed.
function emphasizeCurrentDefinition(){
 const stage=$('#stage'),initialView=isDoubleComplexView();
 const key=state.cover?'cover':initialView?`initial:${state.initialReveal}`:`${state.module}:${state.step}:${state.annotationStep}`;
 if(stage.dataset.definitionKey===key)return;
 stage.dataset.definitionKey=key;definitionAnimations.forEach(a=>a.cancel());definitionAnimations=[];
 if(state.cover||initialView&&state.initialReveal<0||matchMedia('(prefers-reduced-motion:reduce)').matches)return;
 let targets=[];
 if(!$('#pageStack')?.hidden&&['learn','converge'].includes(state.module)){
  const concept=statementMeta().concepts?.[state.annotationStep-1];
  const map=['delta1','delta2','differential'].includes(concept);
  targets=[...document.querySelectorAll(map?'.page-layer.is-current .stack-differential':'.page-layer.is-current .stack-sheet,.page-layer.is-current .stack-point.is-picked .stack-dot')];
 }else{
  targets=[...document.querySelectorAll('#diagram .concept-active')];
  if(initialView&&['delta1','delta2'].includes(initialConcept()))targets.push(...document.querySelectorAll(`#diagram .map-label[data-map-concept="${initialConcept()}"]`));
  if(!targets.length)targets=[...document.querySelectorAll('#diagram .arrow:not(.context-edge),#diagram .diag-box')];
 }
 targets.forEach(el=>{
  if(el.closest('.outside-quadrant'))return;
  const opacity=getComputedStyle(el).opacity,delay=el.closest('.route-2')?150:0;
  el.getAnimations().forEach(a=>a.cancel());
  const animation=el.animate([{opacity:.25},{opacity:1,offset:.45},{opacity}],{duration:650,delay,easing:'ease-out',iterations:1});
  definitionAnimations.push(animation);
 });
 stage.dataset.emphasisCount=String(Number(stage.dataset.emphasisCount||0)+1);
}
