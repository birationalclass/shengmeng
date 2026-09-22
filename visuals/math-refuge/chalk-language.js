import {chalkRuns,mathFont} from './chalk-typography.js?v=22-handwritten-cover';
export function chalkCopy(page,language='zh'){
  return language==='en'?page.en:{title:page.title,text:page.text,source:page.source,author:page.author};
}

export function wrapChalkText(ctx,text,width){
  const words=/[\u3400-\u9fff]/.test(text)?[...text]:text.split(/(\s+)/),lines=[];let line='';
  for(const word of words){if(line&&ctx.measureText(line+word).width>width){lines.push(line.trim());line=word.trimStart();}else line+=word;}
  if(line.trim())lines.push(line.trim());return lines;
}

export function composeChalkPage(ctx,page,index,language,formula){
  const copy=chalkCopy(page,language),font=language==='en'?'RefugeLatin, cursive':'RefugeChinese, RefugeLatin, Kaiti SC, cursive',rows=[];
  ctx.clearRect(0,0,1536,640);ctx.fillStyle='#eee9d5';ctx.textBaseline='alphabetic';
  const runFont=run=>run.math?mathFont:/[\u3400-\u9fff]/.test(run.text)?font:'RefugeLatin, cursive';
  function measure(text,size){return chalkRuns(text).reduce((width,run)=>{ctx.font=`${size}px ${runFont(run)}`;return width+ctx.measureText(run.text).width;},0);}
  function textRow(text,x,y,size,color){
    while(measure(text,size)>1368&&size>24)size--;
    ctx.fillStyle=color;let cursor=x;const chineseSpans=[];
    for(const run of chalkRuns(text)){ctx.font=`${size}px ${runFont(run)}`;ctx.fillText(run.text,cursor,y);const width=ctx.measureText(run.text).width;if(/[\u3400-\u9fff]/.test(run.text))chineseSpans.push([cursor,cursor+width]);cursor+=width;}
    rows.push(Object.assign([x-4,y-size-4,Math.min(1376,cursor-x+8),size+14],{chineseSpans}));
  }
  if(page.kind==='cover'){
    const center=(text,y,size,color='#eee9d5')=>{while(measure(text,size)>1368&&size>24)size--;textRow(text,(1536-measure(text,size))/2,y,size,color);};
    let titleSize=106;while(measure(copy.title,titleSize)>1368&&titleSize>64)titleSize--;
    const lines=wrapChalkText({measureText:t=>({width:measure(t,titleSize)})},copy.title,1368);
    lines.slice(0,2).forEach((line,i)=>center(line,lines.length>1?150+i*82:190,titleSize,'#e4cf9c'));center(copy.author,325,56);
    copy.text.split('\n').forEach((line,i)=>center(line,430+i*52,36));
    return rows;
  }
  textRow(copy.source+'  '+copy.title,84,76,44,'#e4cf9c');
  const [x,y,w,h]=page.rows[2];ctx.drawImage(formula,x+8,y+8,w-16,h-16);rows.push(...(page.formulaRows||[[x,y,w,h]]));
  ctx.font=`36px ${font}`;const notes=wrapChalkText({measureText:text=>({width:measure(text,36)})},copy.text,1344);
  notes.slice(0,3).forEach((line,i)=>textRow(line+(i===2&&notes.length>3?' …':''),88,488+i*42,36,'#eee9d5'));
  return rows;
}
