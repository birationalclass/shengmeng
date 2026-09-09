// Affine projection of (p,q,r). The page index is an organizational axis,
// not a third cochain grading. No map between entire consecutive pages is drawn.
const R=String.raw;
export function pageStackMarkup({start=0,current=0,p=1,q=2,lang='zh',compact=false},math){
 const t=(zh,en)=>lang==='en'?en:zh,colors=['#8fbeff','#71e2d0','#f4c876','#d9b7ec'];
 const count=compact?2:4,baseY=compact?190:350,stepR=compact?235:185,stepP=compact?18:28,stepQ=compact?32:55;
 const point=(i,j,slot)=>[50+42*i+stepR*slot,baseY+stepP*i-stepQ*j];
 const path=(a,b)=>`M${a.join(',')} L${b.join(',')}`;
 const symbol=(x,y,r,ij='',cls='')=>`<text class="stack-math ${cls}" x="${x}" y="${y}">E<tspan baseline-shift="sub" font-size="14">${r}</tspan>${ij?`<tspan baseline-shift="super" font-size="13">${ij}</tspan>`:''}</text>`;
 let out=`<svg viewBox="${compact?'0 0 470 300':'0 0 840 525'}" role="group" aria-label="${t('谱序列各页：p、q、r 三维坐标','Spectral-sequence pages in p, q, r coordinates')}"><defs>`;
 colors.forEach((c,i)=>out+=`<marker id="stack-tip-${i}" markerUnits="userSpaceOnUse" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M1,1 L7,4 L1,7" fill="none" stroke="${c}" stroke-width="1.4" stroke-linecap="round"/></marker>`);
 out+=`<linearGradient id="stack-glass" x1="0" y1="0" x2="1" y2="1"><stop stop-color="#759d9e" stop-opacity=".12"/><stop offset="1" stop-color="#142d39" stop-opacity=".27"/></linearGradient></defs>`;
 out+=`<path id="page-r-axis" class="stack-axis" d="M30,${baseY} H${compact?455:815}" marker-end="url(#stack-tip-0)"/><text class="stack-axis-name" x="${compact?457:817}" y="${baseY-10}">r</text>`;
 if(start>0)out+=`<text class="stack-axis-tick" x="12" y="${baseY+5}">⋯</text>`;
 out+=`<text class="stack-axis-tick" x="${compact?433:788}" y="${baseY-10}">⋯</text>`;
 for(let slot=0;slot<count;slot++){
  const r=start+slot,active=r===current,color=colors[r%4],origin=point(0,0,slot),corners=[[0,0],[4,0],[4,4],[0,4]].map(([i,j])=>point(i,j,slot).join(',')).join(' ');
  out+=`<g class="page-layer ${active?'is-current':''}" data-r="${r}" style="--page-color:${color}"><title>E_${r}; d_${r}: (p,q) → (p+${r},q+${1-r})</title><polygon class="stack-sheet" points="${corners}"/>`;
  for(let i=0;i<=4;i++)out+=`<path class="stack-grid" d="${path(point(i,0,slot),point(i,4,slot))}"/><path class="stack-grid" d="${path(point(0,i,slot),point(4,i,slot))}"/>`;
  for(let i=0;i<=4;i++)for(let j=0;j<=4;j++){
   const [x,y]=point(i,j,slot),selected=i===p&&j===q;
   out+=`<g class="stack-point ${selected?'is-picked':''}" role="button" tabindex="${selected?'0':'-1'}" data-stack-r="${r}" data-stack-p="${i}" data-stack-q="${j}" aria-label="E_${r}^{${i},${j}}"><circle class="stack-hit" cx="${x}" cy="${y}" r="10"/><circle class="stack-dot" cx="${x}" cy="${y}" r="${selected?5:2.6}"/></g>`;
  }
  const target=[p+r,q-r+1],a=point(p,q,slot);
  if(target[0]<=4&&target[1]>=0&&target[1]<=4){
   const b=point(...target,slot),dx=b[0]-a[0],dy=b[1]-a[1],len=Math.hypot(dx,dy),inset=9;
   out+=`<path class="stack-differential" data-source="${p},${q},${r}" data-target="${target.join(',')},${r}" d="${path([a[0]+dx*inset/len,a[1]+dy*inset/len],[b[0]-dx*inset/len,b[1]-dy*inset/len])}" stroke="${color}" marker-end="url(#stack-tip-${r%4})"/><text class="stack-d-label" x="${(a[0]+b[0])/2+6}" y="${(a[1]+b[1])/2-9}">d<tspan baseline-shift="sub" font-size="11">${r}</tspan></text>`;
  }
  out+=symbol(a[0]-19,a[1]-17,r,`${p},${q}`,'point-label');
  out+=`<g class="stack-layer-tab" role="button" tabindex="0" data-stack-r="${r}" aria-pressed="${active}" aria-label="${t('选择第','Select page ')} ${r} ${t('页','')}"><rect x="${origin[0]-8}" y="${compact?7:42}" width="142" height="43" rx="9"/>${symbol(origin[0]+6,compact?35:70,r)}<text class="stack-tab-hint" x="${origin[0]+62}" y="${compact?33:68}">${active?t('当前','Selected'):t('查看','Inspect')}</text></g>`;
  out+=`<path class="stack-tick" d="M${origin[0]},${baseY-4} v8"/><text class="stack-axis-tick" x="${origin[0]-8}" y="${baseY+21}" text-anchor="end">${r}</text></g>`;
 }
 const origin=point(0,0,0);
 out+=`<path class="stack-axis" d="${path(origin,point(4.6,0,0))}"/><path class="stack-axis" d="${path(origin,point(0,4.6,0))}"/><text class="stack-axis-name" x="${point(4.6,0,0)[0]+9}" y="${point(4.6,0,0)[1]+3}">p</text><text class="stack-axis-name" x="${point(0,4.6,0)[0]-24}" y="${point(0,4.6,0)[1]-8}">q</text>`;
 for(let i=1;i<=4;i++){let a=point(i,0,0),b=point(0,i,0);out+=`<text class="stack-axis-tick" x="${a[0]}" y="${a[1]+20}" text-anchor="middle">${i}</text>`;if(i)out+=`<text class="stack-axis-tick" x="${b[0]-12}" y="${b[1]-4}">${i}</text>`;}
 out+='</svg>';
 const targetP=p+current,targetQ=q-current+1;
 let target=targetQ<0?'0':R`E_{${current}}^{${targetP},${targetQ}}`;
 const formula=R`d_{${current}}:E_{${current}}^{${p},${q}}\longrightarrow ${target}`;
 return {svg:out,formula:math(formula),relation:math(R`E_{r+1}\cong H(E_r,d_r)`),note:(targetQ>=0&&(targetP>4||targetQ>4)?t('靶在显示窗口外。','The target is outside the displayed window. '):'')+t('r 是页码；层间不表示线性映射。点的位置表示指标，不表示维数。','r indexes pages; there are no inter-page linear maps. Points encode indices, not dimensions.')};
}
