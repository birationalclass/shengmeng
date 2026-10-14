const pick=(value,language)=>Array.isArray(value)?value[language==='en'?1:0]:value;
export const CHALK_SEMANTIC_COLORS={conclusion:'#93c9ff',caution:'#ffada3'};
export function classroomHeading(page,language,title){return page.classroom&&page.topic?pick(page.topic,language)+' — '+pick(page.subtitle,language):title;}
export function drawReferenceIcon(ctx,kind,x,y,size=22){
 ctx.save();ctx.translate(x,y);ctx.scale(size/24,size/24);ctx.lineWidth=1.8;ctx.strokeStyle=ctx.fillStyle;ctx.beginPath();
 if(kind==='textbook'){ctx.moveTo(12,5);ctx.quadraticCurveTo(7,1,1,4);ctx.lineTo(1,21);ctx.quadraticCurveTo(7,18,12,22);ctx.quadraticCurveTo(17,18,23,21);ctx.lineTo(23,4);ctx.quadraticCurveTo(17,1,12,5);ctx.lineTo(12,22);}
 else{ctx.rect(2,9,13,13);ctx.moveTo(11,2);ctx.lineTo(22,2);ctx.lineTo(22,13);ctx.moveTo(22,2);ctx.lineTo(9,15);}
 ctx.stroke();ctx.restore();
}
export function drawClassroomMetadata(ctx,page,index,language,{exercise=false,total=40}={}){
 ctx.save();ctx.fillStyle='#eee9d5';ctx.textBaseline='alphabetic';ctx.font='18px RefugeLatin, serif';ctx.globalAlpha=.32;ctx.textAlign='right';ctx.fillText(language==='en'?'Page '+(index+1)+' / '+total:'第 '+(index+1)+' / '+total+' 页',1470,625);
 if(!page.classroom){ctx.restore();return;}ctx.fillText(page.source||'§2.6',1470,28);
 if(!page.kind&&!exercise){const ref=page.reference;ctx.textAlign='left';ctx.globalAlpha=.58;if(page.statementOnly){ctx.globalAlpha=1;ctx.fillStyle='#e4cf9c';drawReferenceIcon(ctx,'textbook',84,38,36);ctx.fillStyle='#eee9d5';}else{drawReferenceIcon(ctx,ref?.kind||'extension',84,9);ctx.font='22px RefugeChinese, RefugeLatin, KaiTi, serif';ctx.fillText(pick(ref?.label||['扩展','Extension'],language),116,29);}
  if(page.objective){ctx.globalAlpha=.4;ctx.font='18px "Microsoft YaHei", "Segoe UI", sans-serif';ctx.fillText((language==='en'?'Goal: ':'目标：')+pick(page.objective,language),88,625);}
 }
 ctx.restore();
}
