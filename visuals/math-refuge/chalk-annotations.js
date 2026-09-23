export const CHALK_COLORS={c:'#a8d6df',u:'#e7ce91',b:'#e0aba0'};

// Fixed, slightly uneven strokes: no frame-to-frame random noise or shimmer.
export function drawChalkAnnotation(ctx,rows,annotation,language,{deferStrokes=false}={}){
  if(!annotation||!rows.length)return [];
  const equationRows=rows.filter(r=>r[0]<700);
  const target=equationRows[annotation.row<0?equationRows.length-1:annotation.row]||rows[0];
  const [x,y,w,h]=target,color=CHALK_COLORS[annotation.mark];
  let pad=6;
  for(const other of rows){
    if(other===target||other[0]+other[2]<=x||other[0]>=x+w)continue;
    const gap=other[1]>=y+h?other[1]-y-h:y>=other[1]+other[3]?y-other[1]-other[3]:0;
    pad=Math.min(pad,Math.max(.1,gap*.42));
  }
  if(ctx.save&&ctx.fillRect){
    ctx.save();ctx.globalCompositeOperation='source-atop';ctx.fillStyle=color;
    ctx.fillRect(x,y,w,h);ctx.restore();
  }
  target.chalkColor=color;
  const strokes=[];
  function stroke(points){
    const xs=points.map(p=>p[0]),ys=points.map(p=>p[1]);
    strokes.push(Object.assign([Math.min(...xs)-2,Math.min(...ys)-2,Math.max(...xs)-Math.min(...xs)+4,Math.max(...ys)-Math.min(...ys)+4],{strokePath:points,chalkColor:color,annotation:true}));
    if(!deferStrokes)paintChalkStroke(ctx,points,color);
  }
  if(annotation.mark==='c'){
    // Clockwise dashes, with lifted travel between them. No ellipse or scan reveal.
    const corners=[[x-pad*.5,y-pad*.5],[x+w+pad*.5,y-pad*.5],[x+w+pad*.5,y+h+pad*.5],[x-pad*.5,y+h+pad*.5]];
    corners.forEach((a,edge)=>{
      const b=corners[(edge+1)%4],length=Math.hypot(b[0]-a[0],b[1]-a[1]);
      const count=Math.max(1,Math.round(length/23)),step=length/count;
      for(let i=0;i<count;i++){
        const start=(i*step+2)/length,end=Math.min(1,(i*step+step*.65)/length),points=[];
        for(let k=0;k<=3;k++){
          const t=start+(end-start)*k/3,bend=Math.sin((edge*13+i)*.9+k)*Math.min(.65,pad*.12);
          points.push([a[0]+(b[0]-a[0])*t-(b[1]-a[1])/length*bend,a[1]+(b[1]-a[1])*t+(b[0]-a[0])/length*bend]);
        }
        stroke(points);
      }
    });
  }else if(annotation.mark==='u'){
    stroke(Array.from({length:33},(_,i)=>[x+w*i/32,y+h+pad*.45+Math.sin(i*.36)*pad*.12]));
  }else{
    stroke([[x+10,y-pad*.4],[x-pad*.5,y-pad*.5],[x-pad*.6,y+h+pad*.4],[x+11,y+h+pad*.5]]);
  }
  const cueY=Math.max(185,Math.min(330,y+h/2)),label=annotation.label[language];
  ctx.fillStyle=color;ctx.font=`29px ${language==='zh'?'RefugeChinese':'RefugeLatin'}, cursive`;
  const tokens=language==='zh'?[...label]:label.split(/(\s+)/),lines=[];let line='';
  for(const token of tokens){if(ctx.measureText(line+token).width>250&&line){lines.push(line.trim());line=token.trimStart();}else line+=token;}
  if(line)lines.push(line);
  lines.forEach((text,i)=>ctx.fillText(text,1180,cueY+i*38));
  stroke([[1165,cueY-10],[1142,cueY-7],[1111,cueY-12]]);
  stroke([[1122,cueY-20],[1111,cueY-12],[1123,cueY-5]]);
  return [...strokes,Object.assign([1176,cueY-34,260,Math.max(1,lines.length)*38+12],{chalkColor:color,annotation:true})];
}

export function paintChalkStroke(ctx,points,color){
  if(!points?.length||!ctx.stroke)return;
  ctx.save();ctx.strokeStyle=color;ctx.lineWidth=2.8;ctx.lineCap='round';ctx.lineJoin='round';ctx.beginPath();
  points.forEach(([x,y],i)=>i?ctx.lineTo(x,y):ctx.moveTo(x,y));ctx.stroke();ctx.restore();
}
