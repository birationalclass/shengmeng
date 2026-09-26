export const CHALK_COLORS={c:'#a8d6df',u:'#e7ce91',b:'#e0aba0'};

// Fixed, slightly uneven strokes: no frame-to-frame random noise or shimmer.
export function drawChalkAnnotation(ctx,rows,annotation,language,{deferStrokes=false}={}){
  if(!annotation||!rows.length)return [];
  const equationRows=rows.filter(r=>r[0]<700);
  const target=equationRows[annotation.row<0?equationRows.length-1:annotation.row]||rows[0];
  const [left,top,width,height]=annotation.focus||[0,0,1,1];
  const [tx,ty,tw,th]=target;
  const [x,y,w,h]=[tx+left*tw,ty+top*th,width*tw,height*th],color=CHALK_COLORS[annotation.color||'c'];
  let pad=4;
  for(const other of rows){
    if(other===target||other[0]+other[2]<=x||other[0]>=x+w)continue;
    const gap=other[1]>=y+h?other[1]-y-h:y>=other[1]+other[3]?y-other[1]-other[3]:0;
    pad=Math.min(pad,Math.max(.1,gap*.42));
  }
  // Mark the notation itself; preserve the original white mathematical ink.
  const strokes=[];
  strokes.afterRow=rows.indexOf(target);
  strokes.focusBounds=[x,y,w,h];
  function stroke(points){
    const xs=points.map(p=>p[0]),ys=points.map(p=>p[1]);
    strokes.push(Object.assign([Math.min(...xs)-2,Math.min(...ys)-2,Math.max(...xs)-Math.min(...xs)+4,Math.max(...ys)-Math.min(...ys)+4],{strokePath:points,chalkColor:color,annotation:true}));
    if(!deferStrokes)paintChalkStroke(ctx,points,color);
  }
  {
    // One mark style: clockwise rectangular dashes, with lifted travel between them.
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
  }
  const label=annotation.label?.[language];
  if(!label)return strokes;
  // A short leader joins the frame, rather than floating in a fixed margin.
  const tipX=x+w+pad*.5+7,centerY=y+h/2,noteX=tipX+44,cueY=centerY+10;
  ctx.fillStyle=color;ctx.font=`29px ${language==='zh'?'RefugeChinese':'RefugeLatin'}, cursive`;
  const tokens=language==='zh'?[...label]:label.split(/(\s+)/),lines=[];let line='';
  for(const token of tokens){if(ctx.measureText(line+token).width>Math.min(360,1452-noteX)&&line){lines.push(line.trim());line=token.trimStart();}else line+=token;}
  if(line)lines.push(line);
  lines.forEach((text,i)=>ctx.fillText(text,noteX,cueY+i*35));
  stroke([[noteX-9,centerY-2],[tipX+18,centerY+1],[tipX,centerY]]);
  stroke([[tipX+10,centerY-6],[tipX,centerY],[tipX+10,centerY+5]]);
  strokes.push(Object.assign([noteX-4,cueY-34,Math.max(...lines.map(text=>ctx.measureText(text).width))+8,Math.max(1,lines.length)*35+10],{chalkColor:color,annotation:true}));
  return strokes;
}

export function paintChalkStroke(ctx,points,color,width=2.8){
  if(!points?.length||!ctx.stroke)return;
  ctx.save();ctx.strokeStyle=color;ctx.lineWidth=width;ctx.lineCap='round';ctx.lineJoin='round';ctx.beginPath();
  points.forEach(([x,y],i)=>i?ctx.lineTo(x,y):ctx.moveTo(x,y));ctx.stroke();ctx.restore();
}
