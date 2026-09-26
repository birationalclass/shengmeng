import {kmDiagram} from './km-diagrams.mjs';
import {duanDiagram} from './duan-diagrams.mjs';
// Compact versions of the notebook's first-quadrant diagrams (p right, q up).
// Dots denote terms, not dimensions; the finite drawing window is not truncation.
export const boardDiagrams=new Map([
 [0,{kind:'double',title:'双复形的两种微分',en:'The two double-complex differentials'}],
 [1,{kind:'total',title:'沿总次数对角线取直和',en:'Sum along a total-degree diagonal'}],
 [3,{kind:'filter',title:'列滤过保留右侧分量',en:'Column filtration retains the right-hand terms'}],
 [8,{kind:'differential',title:'第二页微分的双次数 (2,−1)',en:'Page-two differential of bidegree (2,−1)'}],
 [11,{kind:'zero',title:'第零页的纵向微分',en:'Vertical differential on page zero'}],
 [12,{kind:'stable',title:'稳定页沿总次数对角线收敛',en:'Stable-page terms along a total-degree diagonal'}]
]);
export function diagramEdges(kind){
 if(kind==='differential')return [{from:[0,2],to:[2,1],tex:'d_2'}];
 if(kind==='zero')return [0,1,2].map(q=>({from:[1,q],to:[1,q+1],tex:q===1?'d_0':''}));
 if(kind==='double')return [{from:[1,1],to:[2,1],tex:'\\delta_1'},{from:[1,1],to:[1,2],tex:'\\delta_2'},{from:[2,1],to:[2,2],tex:''},{from:[1,2],to:[2,2],tex:''}];
 return [];
}
export function diagramSVG(kind,math){
 const km=kmDiagram(kind,math);if(km)return km;
 const duan=duanDiagram(kind,math);if(duan)return duan;
 const xy=(p,q)=>[60+p*112,267-q*70],gold='#e4cf9c',ink='#eee9d5',blue='#a5dbcf';
 const label=(tex,x,y,size=25)=>math(tex,x,y,size);
 const arrow=([x,y],[u,v],colour)=>{const a=Math.atan2(v-y,u-x),sx=x+9*Math.cos(a),sy=y+9*Math.sin(a),ex=u-11*Math.cos(a),ey=v-11*Math.sin(a);return `<path d="M${sx} ${sy}L${ex} ${ey}m${-10*Math.cos(a-.45)} ${-10*Math.sin(a-.45)}L${ex} ${ey}l${-10*Math.cos(a+.45)} ${-10*Math.sin(a+.45)}" fill="none" stroke="${colour}" stroke-width="2.5" stroke-linecap="round"/>`;};
 if(kind==='canonical'){
   let out=label('X',78,70,42)+label('\\Sigma',385,70,42)+label('Y',78,255,42)+label('C',385,255,42);
   out+=arrow([108,70],[355,70],gold)+arrow([78,100],[78,225],blue)+arrow([385,100],[385,225],blue)+arrow([108,255],[355,255],gold);
   out+=label('\\phi_X',234,42,32)+label('f',44,163,30)+label('h',420,163,30)+label('\\delta',234,286,32);
   return `<svg xmlns="http://www.w3.org/2000/svg" width="480" height="320" viewBox="0 0 480 320">${out}</svg>`;
 }
 let out=`<path d="M39 280H447M46 286V32" fill="none" stroke="${ink}" stroke-width="1.5" opacity=".65"/>`;
 out+=label('p',445,292,24)+label('q',29,25,24);
 if(kind==='filter')out+=`<path d="M263 40H431V280H263Z" fill="${blue}" opacity=".075"/><path d="M265 45V280" stroke="${blue}" stroke-width="2" stroke-dasharray="5 7"/>`;
 if(kind==='total'||kind==='stable')out+=`<path d="M60 57L396 267" stroke="${gold}" stroke-width="15" opacity=".16" stroke-linecap="round"/>`;
 for(let p=0;p<4;p++)for(let q=0;q<4;q++){
   const [x,y]=xy(p,q),active=(kind==='total'||kind==='stable')?p+q===3:kind==='filter'?p>=2:true;
   out+=`<circle cx="${x}" cy="${y}" r="${active?4.5:3}" fill="${active?ink:'#71988a'}" opacity="${active?1:.55}"/>`;
 }
 for(let p=0;p<4;p++)out+=label(String(p),60+p*112,302,19);
 for(let q=1;q<4;q++)out+=label(String(q),24,267-q*70,19);
 for(const e of diagramEdges(kind)){
   const a=xy(...e.from),b=xy(...e.to);out+=arrow(a,b,e.to[0]===e.from[0]?blue:gold);
   if(e.tex)out+=label(e.tex,(a[0]+b[0])/2+(a[0]===b[0]?30:0),(a[1]+b[1])/2-16,25);
 }
 if(kind==='double')out+=label('K^{p,q}',323,30,30);
 if(kind==='total')out+=label('p+q=3',286,30,30);
 if(kind==='filter')out+=label('F^2C^\\bullet',337,25,30);
 if(kind==='differential')out+=label('E_2^{p,q}',320,26,30);
 if(kind==='zero')out+=label('E_0^{p,q}',330,26,30);
 if(kind==='stable')out+=label('E_\\infty^{p,q}',300,28,30)+label('p+q=3',330,92,24);
 return `<svg xmlns="http://www.w3.org/2000/svg" width="480" height="320" viewBox="0 0 480 320">${out}</svg>`;
}
