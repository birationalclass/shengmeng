const R=String.raw;
export const colors={teal:'#70decf',blue:'#93c4ff',gold:'#ffd078',ink:'#edf5f5',muted:'#7697a2',line:'#355762'};
let serial=0;
export function drawDiagram(type,state,lang,math){
const id=`g${++serial}`,out=[],labels=[];let labelOpacity=1;const c=colors;const loc=(a,b)=>lang==='zh'?a:b;
const esc=s=>String(s).replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('"','&quot;');
const line=(x1,y1,x2,y2,color=c.line,width=1,extra='')=>out.push(`<line x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}" stroke="${color}" stroke-width="${width}" ${extra}/>`);
const path=(d,color=c.teal,width=1.5,extra='')=>out.push(`<path d="${d}" stroke="${color}" stroke-width="${width}" fill="none" ${extra}/>`);
const arrow=(x1,y1,x2,y2,color=c.teal,extra='')=>line(x1,y1,x2,y2,color,1.5,`marker-end="url(#${id}-${color===c.gold?'gold':color===c.blue?'blue':color===c.muted?'muted':'teal'})" ${extra}`);
const label=(x,y,tex,w=150,h=40,color=c.ink,size='')=>labels.push(`<div class="diagram-label ${size}" style="left:${x-w/2}px;top:${y-h/2}px;width:${w}px;height:${h}px;color:${color};opacity:${labelOpacity}" data-center="${x},${y}">${math(tex)}</div>`);
const text=(x,y,s,color=c.muted,size=13)=>out.push(`<text x="${x}" y="${y}" text-anchor="middle" fill="${color}" font-size="${size}" font-family="-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif">${esc(s)}</text>`);
const box=(x,y,tex,w=126,h=47,color=c.teal,extra='')=>{out.push(`<g ${extra}><rect x="${x-w/2}" y="${y-h/2}" width="${w}" height="${h}" rx="9" fill="#142d36" stroke="${color}" stroke-opacity=".62"/>`);label(x,y,tex,w-6,h,color);out.push('</g>');};
const dot=(x,y,color=c.teal,r=5,extra='')=>out.push(`<circle cx="${x}" cy="${y}" r="${r}" fill="${color}" ${extra}/>`);
const grid=(kind='K',mode='all',n=3,p0=1)=>{
 const X=p=>110+128*p,Y=q=>367-73*q,sel=state.focus||'h';
 arrow(83,Y(0),714,Y(0),c.muted);arrow(X(0),398,X(0),30,c.muted);label(725,Y(0),'p',25,30,c.muted);label(X(0),20,'q',25,30,c.muted);
 const contour=(degree,lower,color)=>{const pEnd=Math.min(4,degree),qStart=degree-lower;if(lower>pEnd||qStart>4)return;const x1=X(lower),y1=Y(qStart),x2=X(pEnd),y2=Y(degree-pEnd),angle=Math.atan2(y2-y1,x2-x1)*180/Math.PI,len=Math.hypot(x2-x1,y2-y1);out.push(`<rect x="${-41}" y="-28" width="${len+82}" height="56" rx="28" transform="translate(${x1} ${y1}) rotate(${angle})" fill="${color}" fill-opacity=".035" stroke="${color}" stroke-opacity=".75" stroke-dasharray="5 5"/>`);};
 if(['total','D','filtration','leading'].includes(mode)){contour(n,mode==='filtration'||mode==='leading'?p0:0,c.gold);if(mode==='D')contour(n+1,0,c.blue);if(mode!=='leading')label(mode==='filtration'?235:408,425,mode==='filtration'?R`L^{${p0}}C^{${n}}`:R`C^{${n}}:=\operatorname{Tot}^{${n}}K`,330,40,c.gold);}
 // Edges are drawn before opaque cells; no connector crosses a cell interior.
 for(let p=0;p<=4;p++)for(let q=0;q<=4;q++){
  let opacity=mode==='all'?1:.2;const active=p+q===n;
  if(mode==='D'&&active)opacity=1;
  const showH=['all','h','both','total','D','filtration','leading'].includes(mode),showV=['all','v','both','total','D','filtration','leading'].includes(mode);
  if(p<4&&showH){const op=(mode==='h'||mode==='both')?1:opacity;arrow(X(p)+39,Y(q),X(p+1)-40,Y(q),c.teal,`opacity="${op}" data-emphasis="h"`);label((X(p)+X(p+1))/2,Y(q)-13,kind==='K'?'h':R`d_1=\delta`,65,25,c.teal,'tiny');}
  if(p===4&&showH)arrow(X(p)+51,Y(q),X(p)+87,Y(q),c.teal,'stroke-dasharray="3 4" opacity=".55"');
  if(q===4&&showV)arrow(X(p),Y(q)-25,X(p),Y(q)-49,c.blue,'stroke-dasharray="3 4" opacity=".55"');
  if(q<4&&showV){const op=(mode==='v'||mode==='both')?1:opacity;arrow(X(p),Y(q)-21,X(p),Y(q+1)+22,c.blue,`opacity="${op}" data-emphasis="v"`);label(X(p)+20,(Y(q)+Y(q+1))/2,kind==='K'?'v':'d_0',35,25,c.blue,'tiny');}
 }
 for(let p=0;p<=4;p++)for(let q=0;q<=4;q++){
 const highlight=['total','D','filtration','leading'].includes(mode);let active=!highlight||(p+q===n&&p>=(mode==='filtration'||mode==='leading'?p0:0))||(mode==='D'&&p+q===n+1);
 const color=highlight?(p+q===n+1&&mode==='D'?c.blue:c.gold):c.teal;
 const d=kind.endsWith('1')?1:0;
 const term=kind.startsWith('Z')?R`\ker d_${d}^{${p},${q}}`:kind.startsWith('Q')?R`\frac{\ker d_${d}^{${p},${q}}}{\operatorname{im}d_${d}^{${d?p-1:p},${d?q:q-1}}}`:kind==='K'?R`K^{${p},${q}}`:kind==='E_0'?R`E_0^{${p},${q}}`:kind==='E_1'?R`H^{${q}}(X_${p})`:R`E_2^{${p},${q}}`;
 out.push(`<g opacity="${active?1:.22}" class="diagram-hit" data-cell="${p},${q}">`);labelOpacity=active?1:.22;box(X(p),Y(q),term,kind==='E_1'||kind.startsWith('Z')||kind.startsWith('Q')?108:76,kind.startsWith('Q')?53:39,kind.startsWith('Q')?c.gold:active?color:c.muted);labelOpacity=1;out.push('</g>');
 if(mode==='leading'&&p===p0&&p+q===n){dot(X(p)-24,Y(q),c.gold,4);label(X(p),Y(q)+37,R`a_${p}`,60,24,c.gold,'small');}
 }
 if(kind==='E_1'||kind==='E_2'){for(let q=0;q<=4;q++)label(750,Y(q),R`w=${q}`,80,30,[c.teal,c.blue,c.gold,c.teal,c.blue][q],'small');}
 if(mode==='leading')label(430,429,R`a=\sum_{i=${p0}}^{${n}}a_i,\quad Da=0`,430,34,c.ink);
};
const commSquare=(a,b,horizontal,left,right,route=state.route||'top',result='')=>{
 const l=205,r=595,t=122,bottom=332;box(l,t,a,252,68,c.blue);box(r,t,b,245,68,c.teal);box(l,bottom,a,252,68,c.blue);box(r,bottom,b,245,68,c.teal);
 arrow(l+134,t,r-134,t,route==='top'?c.gold:c.teal,`data-route="top"`);arrow(l+134,bottom,r-134,bottom,route==='bottom'?c.gold:c.teal,`data-route="bottom"`);
 arrow(l,t+47,l,bottom-47,route==='bottom'?c.gold:c.blue,`data-route="bottom"`);arrow(r,t+47,r,bottom-47,route==='top'?c.gold:c.teal,`data-route="top"`);
 label(400,t-28,horizontal,145,35,c.teal);label(400,bottom-28,horizontal,145,35,c.teal);label(l-78,229,left,130,50,c.blue);label(r+76,229,right,130,50,c.teal);
 if(result)label(400,410,result,710,43,c.gold);
};
if(type==='comparison'){
box(172,255,R`\operatorname{Gr}_L^pH^n`,240,65,c.blue);box(620,255,R`E_2^{p,q}`,190,65,c.teal);box(400,90,R`E_\infty^{p,q}`,182,59,c.gold);
arrow(223,211,340,126,c.blue);arrow(573,211,460,126,c.teal);arrow(310,255,511,255,c.gold);
label(253,152,R`\rho_{p,q}`,105,45,c.blue);label(548,152,R`\sigma_{p,q}`,115,45,c.teal);label(404,226,R`\alpha_{p,q}=\sigma^{-1}\rho`,267,43,c.gold);
text(166,311,loc('收敛','Convergence'));text(626,311,loc('权重退化','Weight degeneration'));label(400,383,R`\alpha_{p,q}\Phi_L^p=T_2^{p,q}\alpha_{p,q}`,600,55);
}else if(type==='simplicial'){
 const xs=[145,395,645];for(const y of [114,302])for(let p=0;p<3;p++)box(xs[p],y,`X_${p}`,110,53,p===0?c.blue:c.teal);
 for(let p=1;p<=2;p++){for(let i=0;i<=p;i++){let offset=(i-p/2)*19;arrow(xs[p]-64,114+offset,xs[p-1]+64,114+offset,c.teal);arrow(xs[p]-64,302+offset,xs[p-1]+64,302+offset,c.teal);}label((xs[p]+xs[p-1])/2,71,R`d_0^{(${p})},\ldots,d_${p}^{(${p})}`,145,38,c.teal);}
 for(let p=0;p<3;p++){arrow(xs[p],153,xs[p],263,c.blue,`data-emphasis="action"`);label(xs[p]+33,208,`f_${p}`,50,35,c.blue);}
 label(400,404,R`d_i^{(p)}\circ f_p=f_{p-1}\circ d_i^{(p)}`,610,44,c.gold);
}else if(type==='complex'){grid('K',state.focus||'h',state.n||3);}
else if(type==='filtration'){grid('K','filtration',state.n??3,state.p??1);label(579,425,R`W_{${(state.n??3)-(state.p??1)}}H^{${state.n??3}}=L^{${state.p??1}}H^{${state.n??3}}`,330,35,c.gold,'small');}
else if(type==='representative'){grid('K','leading',state.n??3,state.p??1);}
else if(type==='hodge'){
 const w=state.w??2,l=state.ell??1;const X=a=>185+115*a,Y=b=>345-80*b;
 arrow(105,345,710,345,c.muted);arrow(185,400,185,35,c.muted);label(727,345,'a',30,30,c.muted);label(185,20,'b',30,30,c.muted);
 for(let a=0;a<=3;a++)for(let b=0;b<=3;b++){const on=a+b===w;const picked=on&&a>=l;dot(X(a),Y(b),on?(picked?c.gold:c.teal):c.line,on?7:3);if(on)box(X(a),Y(b),R`H^{${a},${b}}`,79,40,picked?c.gold:c.teal);}
 label(437,47,R`\operatorname{Gr}^W_{${w}}V_{\mathbb C}=\bigoplus_{a+b=${w}}H^{a,b}`,535,54,c.teal);
 label(449,412,R`F^{${l}}=\bigoplus_{a\ge${l}}H^{a,${w}-a}`,390,43,c.gold);
}else if(type==='action'){commSquare(R`K^{p,q}`,R`K^{p+1,q}`,'h',R`f_p^*`,R`f_{p+1}^*`,state.route,R`Th=hT,\quad Tv=vT\quad\Longrightarrow\quad TD=DT`);}
else if(type==='pages'){
 const stage=state.page??0;const phase=state.cohom;const d=stage===1?0:1;
 grid(phase?(phase==='kernel'?'Z':'Q')+d:stage===0?'K':stage===1?'E_0':stage===2?'E_1':'E_2',phase?'none':stage===0?'both':stage===1?'v':stage===2?'h':'none');
 label(410,424,phase==='kernel'?R`\ker d_${d}^{p,q}\subseteq E_${d}^{p,q}`:phase==='quotient'?R`E_${d+1}^{p,q}=\ker d_${d}^{p,q}/\operatorname{im}d_${d}^{${d?'p-1':'p'},${d?'q':'q-1'}}`:stage===0?R`K^{p,q}=C^q_{\mathrm{sing}}(X_p,\mathbb Q)`:stage===1?R`E_0^{p,q}\cong K^{p,q},\quad d_0=v`:stage===2?R`E_1^{p,q}=H^q(X_p,\mathbb Q),\quad d_1=\delta`:R`E_2^{p,q}=\ker\delta^{p,q}/\operatorname{im}\delta^{p-1,q}`,690,40);
}else if(type==='degeneration'){
 const r=state.r??2;const pages=[r,r+1,'\\infty'];const px=(k,p)=>82+k*252+p*32,py=(p,q)=>305+p*18-q*48;
 arrow(51,305,778,305,c.muted);label(783,285,'r',25,30,c.muted);
 for(let k=0;k<3;k++){
 const color=[c.blue,c.teal,c.gold][k];box(137+k*252,43,`E_{${pages[k]}}`,105,42,color);
 for(let p=0;p<=4;p++)line(px(k,p),py(p,0),px(k,p),py(p,4),color,.6,'opacity=".38"');
 for(let q=0;q<=4;q++)line(px(k,0),py(0,q),px(k,4),py(4,q),color,.6,'opacity=".38"');
 for(let p=0;p<=4;p++)for(let q=0;q<=4;q++)dot(px(k,p),py(p,q),color,2.3,'opacity=".65"');
 label(px(k,0),330,`${pages[k]}`,35,30,color,'small');
 if(k===0){arrow(px(k,0),py(0,0),px(k,0),76,c.muted);label(px(k,0)-12,70,'q',30,28,c.muted);arrow(px(k,0),py(0,0),px(k,4)+25,py(4,0)+14,c.muted);label(px(k,4)+33,py(4,0)+23,'p',25,25,c.muted);}
 }
 // A higher differential lies within one page, never between page planes.
 const sx=px(0,0),sy=py(0,3),tx=px(0,r),ty=py(r,4-r);
 dot(sx,sy,c.gold,5);dot(tx,ty,c.gold,5);arrow(sx+5,sy+5,tx-5,ty-5,c.gold,`data-emphasis="higher"`);label((sx+tx)/2+38,(sy+ty)/2,R`d_${r}=0`,97,36,c.gold,'small');
 label(281,90,R`\cong`,55,35,c.teal);label(532,90,R`\cong`,55,35,c.teal);
 label(425,422,R`\mathrm{wt}(E_${r}^{0,3})=3,\quad \mathrm{wt}(E_${r}^{${r},${4-r}})=${4-r}`,720,40,c.gold,'small');
 // The selected differential is shown on E_r; all these pages have been identified with E_2.
}else if(type==='convergence'){
 const p=state.p??1,n=state.n??3;const x0=124,y=115;
 for(let i=0;i<=n;i++){const color=i>=p?c.gold:c.muted;box(x0+138*i,y,R`K^{${i},${n-i}}`,103,45,color);if(i<n)label(x0+138*i+69,y,'\\oplus',30,40,c.muted);}
 text(400,56,loc('固定总次数 n 的闭总代表元','A closed total representative in degree n'));
 box(228,245,R`[a]_D+L^{${p+1}}H^{${n}}`,287,68,c.blue);box(626,245,R`[a]_\infty\in E_\infty^{${p},${n-p}}`,273,68,c.gold);
 arrow(383,245,475,245,c.teal);label(429,211,R`\rho_{${p},${n-p}}`,105,40,c.teal);
 label(402,363,R`\frac{L^{${p}}C^{${n}}\cap\ker D}{(L^{${p+1}}C^{${n}}\cap\ker D)+(L^{${p}}C^{${n}}\cap\operatorname{im}D)}`,733,88);
}else if(type==='equivariance'){
 const mode=state.square||'alpha';const info=mode==='rho'?[R`\operatorname{Gr}_L^pH^n`,R`E_\infty^{p,q}`,R`\rho_{p,q}`,R`\Phi_L^p`,R`T_\infty^{p,q}`,R`\rho\Phi_L(\bar a)=[Ta]_\infty=T_\infty\rho(\bar a)`]:mode==='sigma'?[R`E_2^{p,q}`,R`E_\infty^{p,q}`,R`\sigma_{p,q}`,R`T_2^{p,q}`,R`T_\infty^{p,q}`,R`\sigma(T_2z)=(T_2z)_\infty=T_\infty\sigma(z)`]:[R`\operatorname{Gr}_L^pH^n`,R`\dfrac{\ker\delta^{p,q}}{\operatorname{im}\delta^{p-1,q}}`,R`\alpha_{p,q}`,R`\Phi_L^p`,R`T_2^{p,q}`,R`\alpha\Phi_L=T_2\alpha`];
 commSquare(...info.slice(0,5),state.route,info[5]);
}else if(type==='example'){
 const swapped=state.swap||false;const xs=[180,400,620];
 box(xs[0],90,R`D_1\cong\mathbb P^1`,187,55,c.muted);box(xs[1],90,R`P_{ab}`,142,55,c.teal);box(xs[2],90,R`P_{ba}`,142,55,c.blue);
 label(400,30,R`X_1=D_1\sqcup\{P_{ab},P_{ba}\}`,530,40,c.muted);
 xs.forEach((x,i)=>{label(x,171,i===0?'0':i===1?(swapped?'-1':'1'):(swapped?'1':'-1'),75,65,i===0?c.muted:swapped?c.gold:c.teal);});
 path('M405 221 C450 263 572 263 615 221',c.gold,1.5,`marker-end="url(#${id}-gold)"`);label(514,251,'J',45,38,c.gold);
 label(400,317,swapped?R`(0,1,-1)\xmapsto{f_1^*}(0,-1,1)` : R`\ker\delta^{1,0}=\mathbb Q\,(0,1,-1)`,640,60,c.teal);
 label(400,399,R`\alpha_{1,0}\Phi([\eta])=-\alpha_{1,0}([\eta])`,680,43,c.gold);
}else if(type==='descent'){
 box(204,118,'X',160,67,c.blue);box(595,118,R`X_\bullet`,170,67,c.teal);arrow(492,118,303,118,c.teal);label(400,81,R`\pi_\bullet`,120,35,c.teal);
 box(204,282,R`H^n(X,\mathbb Q)`,257,65,c.blue);box(595,282,R`H^n(X_\bullet,\mathbb Q)`,281,65,c.teal);arrow(346,282,441,282,c.gold);label(400,245,R`\pi^*\ \sim`,90,38,c.gold);
 label(400,387,R`\operatorname{Gr}^W_wH^n(X,\mathbb Q)\cong E_2^{n-w,w}`,710,55);
}
const svg=document.createElementNS('http://www.w3.org/2000/svg','svg');svg.setAttribute('viewBox','0 0 800 450');svg.setAttribute('aria-hidden','true');svg.dataset.graph=type;
svg.innerHTML=`<defs>${['teal','blue','gold','muted'].map(name=>`<marker id="${id}-${name}" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M1 1 L7 4 L1 7" fill="none" stroke="${c[name]}" stroke-width="1.2" stroke-linecap="round" stroke-linejoin="round"/></marker>`).join('')}</defs>${out.join('')}`;
const scene=document.createElement('div');scene.className='diagram-scene';scene.dataset.graph=type;scene.append(svg);const overlay=document.createElement('div');overlay.className='diagram-math';overlay.innerHTML=labels.join('');scene.append(overlay);return scene;
}
