// Local page cohomology. These kernels/images are page subspaces, not the
// filtered-complex Z_r and B_r used elsewhere in the notebook.
export function cohomologyView({r,phase,point,mathLabel,t}) {
 const {p,q}=point,ip=p-r,iq=q+r-1,op=p+r,oq=q-r+1;
 const incomingZero=ip<0||iq<0,outgoingZero=op<0||oq<0;
 const E=(a,b)=>a<0||b<0?'0':`E_{${r}}^{${a},${b}}`;
 const names=[t('局部复形','Local complex'),t('闭元：取核','Cocycles: kernel'),t('边界包含于闭元','Boundaries lie in the kernel'),t('同一个上同调类','One cohomology class')];
 let svg='<rect class="co-panel" x="350" y="82" width="470" height="365" rx="14"/>',labels=`<span class="co-title" style="left:370px;top:99px">${names[phase]}</span>`;
 const L=(x,y,tex,cls='',w=130)=>mathLabel(x,y,tex,'co-label '+cls,{width:w,height:36});
 const dot=(x,y,cls='')=>`<circle class="co-element ${cls}" cx="${x}" cy="${y}" r="5"/>`;
 const arrow=(x1,y1,x2,y2,cls='')=>`<path class="co-map ${cls}" d="M${x1},${y1} L${x2},${y2}" marker-end="url(#co-tip)"/>`;
 svg+='<defs><marker id="co-tip" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto" markerUnits="userSpaceOnUse"><path d="M1,1 L7,4 L1,7" fill="none" stroke="#8ed1c4" stroke-width="1.4"/></marker></defs>';
 if(phase<3){
  labels+=L(417,166,E(ip,iq),'co-term',122)+L(585,166,E(p,q),'co-term',122)+L(753,166,E(op,oq),'co-term',122);
  svg+=arrow(471,168,528,168,phase===2?'is-focus':'')+arrow(639,168,696,168,phase===1?'is-focus':'');
  labels+=L(499,143,`d_{${r}}`,'co-map-label',45)+L(667,143,`d_{${r}}`,'co-map-label',45);
 }
 if(phase===0){labels+=L(585,285,`d_{${r}}^{${op},${oq}}d_{${r}}^{${p},${q}}=0`,'co-relation',400);}
 if(phase===1||phase===2){
  svg+='<rect class="co-ambient" x="385" y="214" width="400" height="210" rx="26"/>';
  labels+=L(585,238,E(p,q),'co-ambient-label',220);
  svg+=`<rect class="co-kernel" x="${outgoingZero?394:407}" y="${outgoingZero?255:264}" width="${outgoingZero?382:356}" height="${outgoingZero?161:145}" rx="24"/>`;
  labels+=L(585,285,outgoingZero?`\\ker d_{${r}}=${E(p,q)}`:`\\ker d_{${r}}`,'co-kernel-label',320);
  if(phase===2){svg+='<rect class="co-image" x="427" y="323" width="135" height="55" rx="22"/>';labels+=L(495,350,incomingZero?`\\operatorname{im}d_{${r}}=0`:`\\operatorname{im}d_{${r}}`,'co-image-label',145);}
  svg+=dot(618,330);labels+=L(618,309,'z','',35);
  if(phase===1)labels+=L(629,372,`d_{${r}}z=0`,'co-kernel-label',150);
  if(phase===2&&!incomingZero){svg+='<path class="co-coset" d="M618,330 L683,365"/>'+dot(683,365);labels+=L(692,390,'z+b','',85);}
 }
 if(phase===3){
  svg+='<rect class="co-kernel" x="380" y="212" width="185" height="164" rx="24"/><rect class="co-quotient" x="666" y="238" width="133" height="132" rx="18"/>';
  labels+=L(473,245,`\\ker d_{${r}}`,'co-kernel-label',170)+L(731,269,`E_{${r+1}}^{${p},${q}}`,'co-result-label',130);
  svg+=arrow(580,309,650,309);labels+=L(616,278,'\\pi','',45);
  svg+=dot(416,294)+dot(731,314,'co-class');labels+=L(416,271,'z','',32)+L(731,347,'[z]','',70);
  if(!incomingZero){svg+=dot(523,339);labels+=L(523,362,'z+b','',80);}
  svg+=`<circle class="co-traveller" data-dx="315" data-dy="20" cx="416" cy="294" r="5"/>`;
  if(!incomingZero)svg+='<circle class="co-traveller" data-dx="208" data-dy="-25" cx="523" cy="339" r="5"/>';
  labels+=L(585,413,incomingZero?'\\pi(z+0)=\\pi(z)=[z]':'\\pi(z+b)=\\pi(z)=[z]','co-equivalence',430);
 }
 return {svg:`<g class="cohomology-focus" data-co-phase="${phase}">${svg}</g>`,labels:`<div class="cohomology-labels">${labels}</div>`,incomingZero,outgoingZero};
}

export function cohomologyExposition({r,phase,point,math,t}) {
 const {p,q}=point,ip=p-r,iq=q+r-1,op=p+r,oq=q-r+1;
 const E=(a,b)=>a<0||b<0?'0':`E_{${r}}^{${a},${b}}`,map=`d_{${r}}^{${p},${q}}`,input=`d_{${r}}^{${ip},${iq}}`;
 const formula=[
  [`${E(ip,iq)}\\xrightarrow{d_{${r}}}${E(p,q)}\\xrightarrow{d_{${r}}}${E(op,oq)}`,`d_{${r}}^2=0`],
  [`\\ker ${map}=\\{z\\in ${E(p,q)}:${map}z=0\\}`],
  [`\\operatorname{im}(${input})\\subseteq\\ker(${map})`,`b=d_{${r}}y\\quad\\Longrightarrow\\quad d_{${r}}b=0`],
  [`E_{${r+1}}^{${p},${q}}\\cong\\frac{\\ker(${map})}{\\operatorname{im}(${input})}`,`z\\sim z+b\\quad(b\\in\\operatorname{im}d_{${r}})`]
 ][phase];
 const notes=[r===0?t('固定一列，使用 d₀=δ₂；对每个位置做同样的构造。','Fix a column and use d₀=δ₂. Apply the same construction at every position.'):t('两个箭头都是当前页的微分，次数为 (r,1−r)。','Both arrows are differentials on the current page, of bidegree (r,1−r).'),t('只取被流出微分送到零的元素。区域示意包含关系，不表示维数。','Keep elements killed by the outgoing differential. Regions indicate inclusion, not dimension.'),t('流入微分的像属于核，因为 dᵣ²=0。','The incoming image lies in the kernel because dᵣ²=0.'),r===0?t('逐列取上同调组成 E₁。商映射的定义域是 ker d₀。','Column cohomology assembles E₁. The quotient map is defined on ker d₀.'):t('在每个 (p,q) 取这个商，组成下一页；新微分由总微分 D 诱导。','Take this quotient at every (p,q) to form the next page; its new differential is induced by D.')];
 if(phase===3&&r===0)formula.push('E_1^{p,q}=H^q(E_0^{p,\\bullet},d_0)\\cong H^q(K^{p,\\bullet},\\delta_2)');
 return `<div class="operation-content evolution-exposition">${formula.map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}</div><p class="operation-note">${notes[phase]}</p>`;
}
