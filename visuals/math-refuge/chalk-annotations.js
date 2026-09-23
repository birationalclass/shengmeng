export const CHALK_COLORS={c:'#a8d6df',u:'#e7ce91',b:'#e0aba0'};

// Fixed, slightly uneven strokes: no frame-to-frame random noise or shimmer.
export function drawChalkAnnotation(ctx,rows,annotation,language){
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
  if(ctx.beginPath&&ctx.stroke){
    ctx.save();ctx.strokeStyle=color;ctx.lineWidth=2.8;ctx.lineCap='round';ctx.lineJoin='round';ctx.beginPath();
    if(annotation.mark==='c'){
      for(let i=0;i<=72;i++){
        const angle=-.15+i/72*Math.PI*2.035;
        const px=x+w/2+(w/2+pad*.5+Math.sin(i*.7)*pad*.1)*Math.cos(angle);
        const py=y+h/2+(h/2+pad*.5)*Math.sin(angle)+Math.sin(i*.45)*pad*.12;
        if(i)ctx.lineTo(px,py);else ctx.moveTo(px,py);
      }
    }else if(annotation.mark==='u'){
      for(let i=0;i<=32;i++){
        const px=x+w*i/32,py=y+h+pad*.45+Math.sin(i*.36)*pad*.12;
        if(i)ctx.lineTo(px,py);else ctx.moveTo(px,py);
      }
    }else{
      ctx.moveTo(x+10,y-pad*.4);ctx.lineTo(x-pad*.5,y-pad*.5);ctx.lineTo(x-pad*.6,y+h+pad*.4);ctx.lineTo(x+11,y+h+pad*.5);
    }
    ctx.stroke();ctx.restore();
  }
  // The marked region is revealed with its equation, never over a later line.
  target[0]-=pad;target[1]-=pad;target[2]+=2*pad;target[3]+=2*pad;
  target.chalkColor=color;
  const cueY=Math.max(185,Math.min(330,y+h/2)),label=annotation.label[language];
  ctx.fillStyle=color;ctx.font=`29px ${language==='zh'?'RefugeChinese':'RefugeLatin'}, cursive`;
  const tokens=language==='zh'?[...label]:label.split(/(\s+)/),lines=[];let line='';
  for(const token of tokens){if(ctx.measureText(line+token).width>250&&line){lines.push(line.trim());line=token.trimStart();}else line+=token;}
  if(line)lines.push(line);
  lines.forEach((text,i)=>ctx.fillText(text,1180,cueY+i*38));
  if(ctx.stroke){
    ctx.save();ctx.strokeStyle=color;ctx.lineWidth=2.7;ctx.lineCap='round';ctx.beginPath();
    ctx.moveTo(1165,cueY-10);ctx.lineTo(1142,cueY-7);ctx.lineTo(1111,cueY-12);
    ctx.moveTo(1122,cueY-20);ctx.lineTo(1111,cueY-12);ctx.lineTo(1123,cueY-5);ctx.stroke();ctx.restore();
  }
  return [Object.assign([1106,cueY-34,330,Math.max(1,lines.length)*38+12],{chalkColor:color})];
}
