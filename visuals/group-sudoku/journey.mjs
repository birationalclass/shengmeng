export const PLACES=[[-43,20],[-27,-9],[2,-25],[32,-19],[48,10],[21,28],[-7,14],[-23,45]];
export const THEMES=[
 {name:'乌木金线',paper:'#30251c',ink:'#f5e3b2',given:'#b5a17b',line:'#bc995777',rim:0xc7a261,frame:0x493226,motif:2},
 {name:'青玉回纹',paper:'#173c36',ink:'#e0edce',given:'#8ead9c',line:'#a2bba26f',rim:0x83af91,frame:0x224c41,motif:3},
 {name:'冰湖银霜',paper:'#adcfde',ink:'#173e58',given:'#244861',line:'#35637da0',rim:0xc8e4ed,frame:0x6baac7,motif:4},
 {name:'绛红鎏金',paper:'#4a2527',ink:'#efdab0',given:'#b89785',line:'#b99a6577',rim:0xd0a356,frame:0x572e2c,motif:5},
 {name:'玄铁黄铜',paper:'#263138',ink:'#e4d1a0',given:'#99a8aa',line:'#b2a17470',rim:0xb09057,frame:0x344047,motif:6},
 {name:'星穹圣殿',paper:'#1d2943',ink:'#e0e4eb',given:'#9faaca',line:'#9caccd77',rim:0xa9b4ce,frame:0x273453,motif:7},
 {name:'魔法学院',paper:'#24352c',ink:'#e5ce9b',given:'#9baf94',line:'#b79a6177',rim:0xb5894e,frame:0x3b4332,motif:8},
 {name:'紫檀金嵌',paper:'#34213b',ink:'#f2dcad',given:'#b79da9',line:'#c0a37480',rim:0xdbc078,frame:0x4a2b39,motif:9}
];
export const clamp=x=>Math.max(0,Math.min(1,x));
export const ease=x=>{x=clamp(x);return x*x*(3-2*x)};
export const stageTime={assembly:6.4,bridge:3.1,flight:4.2};
export function frontier(completed){for(let n=2;n<=9;n++)if(!completed.includes(n))return n;return 9;}
export function canEnter(n,completed){return n>=2&&n<=frontier(completed);}
// The endpoint tangent is zero; intermediate camera keys carry velocity through
// each shot, following the time-scaled Hermite crane used by the test module.
export function cameraSpline(keys,t){let i=0;while(i<keys.length-2&&t>keys[i+1][0])i++;const a=keys[i],b=keys[i+1],p=keys[Math.max(0,i-1)],q=keys[Math.min(keys.length-1,i+2)],d=b[0]-a[0],u=clamp((t-a[0])/d),h0=2*u**3-3*u*u+1,h1=u**3-2*u*u+u,h2=-2*u**3+3*u*u,h3=u**3-u*u;return [1,2].map(k=>a[k].map((v,j)=>h0*v+h1*d*(i===0?0:(b[k][j]-p[k][j])/(b[0]-p[0]))+h2*b[k][j]+h3*d*(i===keys.length-2?0:(q[k][j]-a[k][j])/(q[0]-a[0]))));}

export function arrivalPhase(t,wasBuilt=false){return t<2.8?'moving':wasBuilt?'ready':t<3?'settled':t<5.05?'building':t<6.4?'board':'ready';}

// Nameplates sit centered below the circular platform, on the surrounding map.
export function plaqueOffset(){return [0,14.5];}
