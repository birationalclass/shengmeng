import {previousGuang} from './guang-previous.js';
import {wind as previousWind} from './wind-data.js';
import {windReference} from './wind-reference.js';

// Authored in 3D while studying the smooth blades / pressed shoulders / lifted
// tips of BV1PP4y1Z7Zv. This 广 is a local design, not an identified original
// character or a recovered model from that video.
function brush(name,stations,front,back,options={}){
 const a=[],b=[];
 stations.forEach(([x,y,z,r,bank],i)=>{
  const before=stations[Math.max(0,i-1)],after=stations[Math.min(stations.length-1,i+1)],dx=after[0]-before[0],dy=after[1]-before[1],length=Math.hypot(dx,dy)||1;
  const nx=-dy/length*Math.cos(bank),ny=dx/length*Math.cos(bank),nz=Math.sin(bank);
  a.push([x-nx*r,y-ny*r,z-nz*r]);b.push([x+nx*r,y+ny*r,z+nz*r]);
 });
 return {name,a,b,front,back,brush:'sculpted-lens-v3',crown:[.46,.58,.52],rearCrown:[.5,.45,.52],camber:[0,.03,-.015,0],sectionPower:[2.15,2.65,2.4,2.1],capStart:.025,capEnd:.035,motion:[0,.035,.18,.4,.68,.9,1],...options};
}
const strokes=[
 brush('广 · 侧点铺锋',[
  [-.07,1.84,-.24,.025,-.55],
  [.08,1.82,-.20,.09,-.40],
  [.25,1.66,-.03,.20,-.08],
  [.39,1.45,.16,.23,.28],
  [.42,1.27,.24,.15,.64],
  [.37,1.22,.23,.08,.88]
 ],[.20,.34,.40,.30],[.12,.19,.23,.18],{capStart:.07,capEnd:.10,crown:[.38,.63,.56],start:.06,end:.48,motion:[0,.05,.22,.63,.9,1]}),
 brush('广 · 横势逆入提收',[
  [-1.13,.62,-.29,.03,-.44],
  [-1.14,.76,-.31,.09,-.30],
  [-.99,.78,-.28,.17,-.18],
  [-.54,.81,-.12,.18,-.02],
  [.05,.90,.05,.15,.16],
  [.61,1.00,.18,.17,.35],
  [1.03,1.03,.26,.22,.59],
  [1.34,.99,.27,.21,.85],
  [1.47,.88,.21,.12,1.05],
  [1.48,.82,.17,.075,1.15]
 ],[.15,.22,.19,.16,.28,.34,.25],[.10,.12,.11,.10,.16,.19,.15],{capStart:.015,capEnd:.065,camber:[0,.045,-.05,.045,0],crown:[.4,.6,.45,.66,.5],start:.53,end:1.20,motion:[0,.025,.10,.37,.72,.87,1]}),
 brush('广 · 长撇行锋回挑',[
  [-1.03,.76,-.20,.05,-.12],
  [-.86,.53,-.18,.18,-.10],
  [-.83,.17,-.08,.22,-.29],
  [-.87,-.25,.10,.25,-.55],
  [-1.01,-.70,.31,.28,-.82],
  [-1.23,-1.10,.48,.27,-1.02],
  [-1.48,-1.39,.48,.21,-1.22],
  [-1.72,-1.56,.30,.12,-1.40],
  [-1.88,-1.55,.01,.055,-1.57],
  [-1.99,-1.40,-.17,.002,-1.72]
 ],[.19,.25,.29,.28,.24,.17,.08],[.11,.15,.17,.17,.15,.11,.05],{capStart:.02,capEnd:0,camber:[0,.035,-.045,.065,.01,0],crown:[.42,.57,.62,.48],rearCrown:[.52,.45,.48],start:1.27,end:2.55,motion:[0,.025,.13,.36,.64,.87,.96,1]})
];
export const guang={id:'guang',text:'广',title:'铺锋',subtitle:'侧点铺开，长撇翻转回挑',kind:'rail',detailLevel:'sculpted',strokes,
 legacyStrokes:previousGuang.strokes.map((s,i)=>({...s,name:strokes[i].name,start:strokes[i].start,end:strokes[i].end})),
 duration:6,writeStart:.06,writeEnd:2.55,frontalAt:4.25,requiresLicense:true,
 source:{name:'广 · 三笔独立塑形',phrase:'宽笔面、薄圆边、侧锋翻转；不使用通用字的原轮廓',url:'https://www.bilibili.com/video/BV1PP4y1Z7Zv/',image:'',caption:'本地重新设计；非原视频广字模型',description:'三笔的轮廓、前后厚度、铺锋、折肩、收锋与空间轨迹独立设计。以原视频中的平滑宽面、圆厚边缘和叶状翻转为观察依据；没有取得原作者模型，也不将本地广字称作原作逐点复刻。'}};

export const brushGlyphs=[guang];

// The right-hand outer hook of 風: specifically reworked after comparing the
// reference at 7.74 s and 8.63 s. The thin upright opens into a broad scooped
// face; the terminal turns upward and behind the rim. Both boundary splines
// share the rising terminal, so the upturn is part of the continuous gesture.
const oldHook=previousWind.strokes[1],hookA=[],hookB=[],hookCenters=[],hookDeltas=[];
oldHook.a.forEach((p,i)=>{
 const other=oldHook.b[i],c=p.map((n,j)=>(n+other[j])*.5),d=other.map((n,j)=>(n-p[j])*.5);
 const spread=[1,1,1,1,1,1,1,1,1,1,1,1,1.40,1.55,1.50,1.10,1.30,1][i];
 if(i===15){c[0]=1.50;c[1]=-1.58;c[2]=.20;}
 if(i===16){c[0]=1.72;c[1]=-1.44;c[2]=.02;}
 if(i===17){c[0]=1.70;c[1]=-1.13;c[2]=-.24;}
 hookCenters.push(c);hookDeltas.push(d.map(n=>n*spread));
});
hookCenters.forEach((c,i)=>{
 let d=hookDeltas[i];
 if(i>=13){
  // Continue the section frame around the bend. Reusing the descending
  // section direction on an ascending tip would pinch the paired rails.
  const before=hookCenters[i-1],after=hookCenters[Math.min(hookCenters.length-1,i+1)],t=after.map((v,k)=>v-before[k]),len=Math.hypot(...t);t.forEach((v,k)=>t[k]=v/len);
  const xy=Math.hypot(t[0],t[1]),side=[-t[1]/xy,t[0]/xy,0],binormal=[-t[2]*side[1],t[2]*side[0],t[0]*side[1]-t[1]*side[0]];
  const bank=[-.10,-.22,-.38,-.62,-.72][i-13],radius=[.36,.37,.23,.12,.055][i-13];
  d=side.map((v,k)=>radius*(v*Math.cos(bank)+binormal[k]*Math.sin(bank)));
 }
 hookA.push(c.map((n,j)=>n-d[j]));hookB.push(c.map((n,j)=>n+d[j]));
});
const hook={...oldHook,a:hookA,b:hookB,brush:'sculpted-lens-v3',role:'wind-main',
 front:[.28,.32,.26,.24,.33,.36,.30,.18,.10,.075,.065,.055,.050,.055,.060,.065,.075,.090,.13,.22,.25],
 back:[.16,.20,.17,.14,.18,.22,.18,.11,.065,.045,.040,.035,.035,.035,.040,.045,.050,.070,.11,.18,.22],
 crown:[.46,.53,.57,.51,.48,.55,.63,.57,.50],rearCrown:[.48,.50,.52],
 camber:[0,.015,.015,0,0,0,0,0,0,0,0,0,0,.015,.025,.01,-.04,-.065,-.085,-.06,0],
 sectionPower:[2.15,2.2,2.2,2.6,2.9,3.0,2.7,2.2],capStart:0,capEnd:.022,safeBend:true,
 motion:[0,.05,.21,.44,.66,.79,.88,.94,.975,1]};
const mainGesture={
 timing:[[0,0],[.10,.055],[.25,.22],[.40,.29],[.54,.49],[.67,.73],[.78,.88],[.90,.945],[.97,.979],[1,1]],
 wake:.16,leadingEdge:-.55,pressure:[.35,.85,.95,.50,.32,.60,1.15,1.10,.30],roll:[-.12,-.26,.12,.16,-.08,.10,.28,-.12,0],
 phases:[[0,'逆入蓄势'],[.12,'转锋折肩'],[.30,'提锋下行'],[.67,'按笔铺开'],[.89,'回锋上挑']]
};
const timing=[
 [.06,.29],[.31,1.12],[1.12,1.52],[1.53,1.64],[1.65,1.89],[1.90,2.01],[2.02,2.26],[2.27,2.44],[2.48,2.62]
];
const windStrokes=previousWind.strokes.map((s,i)=>{
 const stroke=i===1?hook:s;
 const gesture=i===1?mainGesture:{timing:[[0,0],[.12,.045],[.35,.27],[.66,.75],[.87,.95],[1,1]],wake:.085,leadingEdge:i%2?.25:-.25,pressure:[.35,.85,1,.65,.20],roll:[-.12,.14,-.08,.10,0],phases:[[0,'承势入笔'],[.18,'行锋'],[.82,'提锋接势']]};
 return {...stroke,start:timing[i][0],end:timing[i][1],gesture,...(i===2?{role:'wind-inner',connection:{from:'wind-main'},name:'内撇 · 接第二笔'}:{})};
});
export const windJoin7={...previousWind,strokes:windStrokes,writeEnd:2.62,legacyStrokes:previousWind.strokes,
 revision:'wind-stroke-two-to-three-20261024',method:'Explicit lifted hairline from stroke 2 to stroke 3, joining the actual section endpoints and tangents. Authored gesture timing and local pressure. Other stroke contours retained; no original artist mesh or recovered keyframes.'};
export const windStudy=windReference;
