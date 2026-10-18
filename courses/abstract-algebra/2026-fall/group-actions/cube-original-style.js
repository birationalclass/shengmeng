// Adapted from the original promo's drawRubik: perspective, dark cubie bodies,
// RCOL palette, directional lighting, sticker sheen, floor reflection, debris.
const ORIGINAL_CUBE_COLORS=['#ff8a1f','#e8313c','#ffd500','#f5f5f5','#1f6fe0','#18b35a'];
function cubeDust(t){ctx.save();for(let j=0;j<65;j++){const z=((hash1(j+32)*30-t*(.5+hash1(j+8))*1.1)%30+30)%30+4,s=420/z,x=960+(hash1(j*3+1)-.5)*30*s*1.3,y=560+(hash1(j*3+2)-.5)*18*s;ctx.globalAlpha=clamp((34-z)/10)*clamp((z-4)/4)*.28;ctx.fillStyle=ORIGINAL_CUBE_COLORS[j%6];ctx.save();ctx.translate(x,y);ctx.rotate(j+t*.15);ctx.fillRect(-s*.32,-s*.32,s*.64,s*.64);ctx.restore()}ctx.restore()}
function cubeDraw(t,{x=650,y=590,size=110,pieces=M.cube(),view=-.6}={}){
 const pitch=.45,D=11,F=size*11,viewPoint=v=>M.rotate(M.rotate(v,'y',view),'x',pitch),light=[-.35,.6,.72],scale=size/100;
 const shade=(hex,k)=>{const n=parseInt(hex.slice(1),16);return `rgb(${Math.min(255,((n>>16)&255)*k)|0},${Math.min(255,((n>>8)&255)*k)|0},${Math.min(255,(n&255)*k)|0})`};
 const polygon=ps=>{ctx.beginPath();ps.forEach((p,i)=>ctx[i?'lineTo':'moveTo'](p[0],p[1]));ctx.closePath()};
 const render=mirror=>{const faces=[],floor=-1.75;const reflect=v=>mirror?[v[0],2*floor-v[1],v[2]]:v;
  for(const p of pieces){const frame=p.frame||[[1,0,0],[0,1,0],[0,0,1]];for(let axis=0;axis<3;axis++)for(const sign of [-1,1]){
   const n=M.scale(frame[axis],sign),center=M.add(p.pos,M.scale(n,.5)),u=frame[(axis+1)%3],v=frame[(axis+2)%3],corners=(off,h)=>[[-1,-1],[1,-1],[1,1],[-1,1]].map(([a,b])=>M.add(p.pos,M.add(M.scale(n,off),M.add(M.scale(u,a*h),M.scale(v,b*h)))));
   const N=viewPoint(mirror?[n[0],-n[1],n[2]]:n),cen=viewPoint(reflect(center));if(M.dot(N,[-cen[0],-cen[1],D-cen[2]])<=0)continue;
   const prj=ps=>ps.map(w=>{const q=viewPoint(reflect(w));return [x+F*q[0]/(D-q[2]),y-F*q[1]/(D-q[2])]});
   const sticker=p.stickers.find(s=>M.dot(s.normal,n)>.999),lit=.5+.5*Math.max(0,M.dot(N,light));
   faces.push({z:cen[2],body:prj(corners(.5,.49)),st:sticker?prj(corners(.503,.405)):null,col:sticker?.color,lit,highlight:p.highlight});
  }}faces.sort((a,b)=>a.z-b.z);ctx.save();ctx.lineJoin='round';
  for(const f of faces){const yy=f.body.reduce((s,p)=>s+p[1],0)/4;ctx.globalAlpha=mirror?.19*(1-sstep(805,895,yy)):1;if(ctx.globalAlpha<.002)continue;polygon(f.body);ctx.fillStyle='#0b0b0f';ctx.fill();ctx.strokeStyle='#0b0b0f';ctx.lineWidth=2;ctx.stroke();if(!f.st)continue;polygon(f.st);const col=shade(f.col,f.lit);ctx.fillStyle=col;ctx.fill();ctx.strokeStyle=f.highlight?'#ff8dbe':col;ctx.lineWidth=f.highlight?3.6:3*scale;ctx.stroke();const a=f.st[0],b=f.st[2],g=ctx.createLinearGradient(a[0],a[1],b[0],b[1]);g.addColorStop(0,`rgba(255,255,255,${.3*f.lit})`);g.addColorStop(.45,'rgba(255,255,255,0)');ctx.fillStyle=g;ctx.fill()}
  ctx.restore();
 };
 ctx.save();ctx.globalCompositeOperation='lighter';glowDot(x,y,480,'rgba(120,170,255,A)',.17);const floorLight=ctx.createRadialGradient(x,y+230,0,x,y+230,420);floorLight.addColorStop(0,'rgba(120,160,230,.11)');floorLight.addColorStop(1,'rgba(0,0,0,0)');ctx.fillStyle=floorLight;ctx.fillRect(x-420,y+100,840,220);ctx.restore();render(true);render(false);
}
