import {inlineInk,drawInlineInk} from './chalk-inline-math.js?v=inline-root-1';
import {chalkInlineRuns,mathFont} from './chalk-typography.js?v=inline-root-1';
import {drawChalkAnnotation} from './chalk-annotations.js?v=report-line-sync-6';
import {explainedFlow} from './flow-explanation.js?v=report-line-sync-6';
import {wrapBoardText} from './chalk-wrap.js?v62-chalk-ink';
export function chalkCopy(page,language='zh',{board=false}={}){
  return language==='en'?{...page.en,text:!board&&page.en.readingText||page.en.text}:{title:page.title,text:!board&&page.readingText||page.text,source:page.source,author:page.author};
}

export function wrapChalkText(ctx,text,width){
  return wrapBoardText(text,1,width,t=>ctx.measureText(t).width);
}

export function composeChalkPage(ctx,page,index,language,formula,options={}){
  const copy=chalkCopy(page,language,{board:true}),font=language==='en'?'RefugeLatin, cursive':'RefugeChinese, RefugeLatin, Kaiti SC, cursive',rows=[];
  ctx.clearRect(0,0,1536,640);ctx.fillStyle='#eee9d5';ctx.textBaseline='alphabetic';
  const runFont=(run,heading=false)=>run.math&&!(heading&&/^\d+(?:\.\d+)*[.)]?$/.test(run.text))?mathFont:/[\u3400-\u9fff]/.test(run.text)?font:'RefugeLatin, cursive';
  const measurements=new Map();
  function bounds(text,size,heading=false){
    const key=size+':'+heading+':'+text;if(measurements.has(key))return measurements.get(key);
    let advance=0,left=0,right=0,ascent=0,descent=0;
    for(const run of chalkInlineRuns(text)){
      const px=size*(run.script?.7:1),dy=run.script==='sub'?size*.22:run.script==='sup'?-size*.4:0;
      ctx.font=`${px}px ${runFont(run,heading)}`;const ink=inlineInk(ctx,run,px);
      left=Math.min(left,advance-(ink.actualBoundingBoxLeft??0));right=Math.max(right,advance+(ink.actualBoundingBoxRight??ink.width));
      ascent=Math.max(ascent,(ink.actualBoundingBoxAscent??px*.8)-dy);descent=Math.max(descent,(ink.actualBoundingBoxDescent??px*.3)+dy);advance+=ink.width;
    }
    const value={advance,left,right,ascent,descent};measurements.set(key,value);return value;
  }
  function measure(text,size,heading=false){return bounds(text,size,heading).advance;}
  measure.bounds=bounds;
  function textRow(text,x,y,size,color,heading=false){
    while(measure(text,size,heading)>1368&&size>24)size--;
    ctx.fillStyle=color;let cursor=x;const chineseSpans=[];
    for(const run of chalkInlineRuns(text)){ctx.font=`${size*(run.script ? .7 : 1)}px ${runFont(run,heading)}`;drawInlineInk(ctx,run,cursor,y+(run.script==='sub'?size*.22:run.script==='sup'?-size*.4:0),size*(run.script?.7:1));const width=inlineInk(ctx,run,size*(run.script?.7:1)).width;if(/[\u3400-\u9fff]/.test(run.text))chineseSpans.push([cursor,cursor+width]);cursor+=width;}
    const ink=bounds(text,size,heading);
    rows.push(Object.assign([x+ink.left-4,y-ink.ascent-4,ink.right-ink.left+8,ink.ascent+ink.descent+8],{chineseSpans,chalkColor:color}));
  }
  if(page.kind==='closing'){textRow(copy.title,(1536-measure(copy.title,124))/2,360,124,'#e4cf9c');return rows;}
  if(page.kind==='cover'){
    const center=(text,y,size,color='#eee9d5')=>{while(measure(text,size)>1368&&size>24)size--;textRow(text,(1536-measure(text,size))/2,y,size,color);};
    let titleSize=106;while(measure(copy.title,titleSize)>1368&&titleSize>64)titleSize--;
    let lines=wrapChalkText({measureText:t=>({width:measure(t,titleSize)})},copy.title,1368);
    if(options.authored){
      let height;
      do{lines=wrapChalkText({measureText:t=>({width:measure(t,titleSize)})},copy.title,1368);height=lines.reduce((sum,line)=>{const b=bounds(line,titleSize);return sum+b.ascent+b.descent;},0)+Math.max(0,lines.length-1)*18;if(lines.length<=2&&height<=178)break;titleSize-=2;}while(titleSize>28);
      let top=80+(178-height)/2;for(const line of lines){const b=bounds(line,titleSize);center(line,top+b.ascent,titleSize,'#e4cf9c');top+=b.ascent+b.descent+18;}
    }else lines.slice(0,2).forEach((line,i)=>center(line,lines.length>1?150+i*82:190,titleSize,'#e4cf9c'));
    center(copy.author,325,56);
    copy.text.split('\n').forEach((line,i)=>center(line,430+i*52,36));
    return rows;
  }
  if(!page.hideHeading&&!options.hideHeading){textRow(copy.source+'  '+copy.title,84,76,44,'#e4cf9c',true);rows.at(-1).mainLine=0;}
  if(!page.diagram&&(page.layout==='flow'||!page.annotation)){
    const items=explainedFlow(page,language,measure,options.hideHeading);
    const formulaRects=items.filter(i=>i.source).map(i=>Object.assign([...i.rect],{formulaRow:i.index}));
    const cues=drawChalkAnnotation(ctx,formulaRects,page.annotation,language,options);
    for(const item of items){
      if(item.source){
        let source=item.source;
        if(page.layout!=='flow'){
          const [x,y,w,h]=page.rows[2],sx=(formula.naturalWidth||formula.width||w)/(w-16),sy=(formula.naturalHeight||formula.height||h)/(h-16);
          source=[(source[0]-x-8)*sx,(source[1]-y-8)*sy,source[2]*sx,source[3]*sy];
        }
        ctx.drawImage(formula,...source,...item.rect);
        rows.push(Object.assign([...item.rect],{formulaRow:item.index,mainLine:item.mainLine}));
        if(item.index===cues.afterRow)rows.push(...cues.map(c=>Object.assign(c,{mainLine:item.mainLine})));
      }else{
        textRow(item.text,item.x,item.y,item.size,'#eee9d5');
        rows.at(-1).prose=item.role;rows.at(-1).mainLine=item.mainLine;
      }
    }
    return rows;
  }
  const [x,y,w,h]=page.rows[2];
  ctx.drawImage(formula,x+8,y+8,w-16,h-16);
  const formulaRows=(page.formulaRows||[[x,y,w,h]]).map(([a,b,c,d],i)=>Object.assign([a,b,c-.00001,d-.00001],{formulaRow:i}));
  const cues=drawChalkAnnotation(ctx,formulaRows,page.annotation,language,options);
  // Annotate immediately after the defining line, before the next equation.
  formulaRows.forEach((row,i)=>{rows.push(row);if(i===cues.afterRow)rows.push(...cues);});
  let noteSize=36,notes=wrapChalkText({measureText:text=>({width:measure(text,noteSize)})},copy.text,1344);
  while(notes.length>3&&noteSize>26){noteSize--;notes=wrapChalkText({measureText:text=>({width:measure(text,noteSize)})},copy.text,1344);}
  // Leave room for descenders and inline scripts: reveal rectangles must not overlap.
  notes.forEach((line,i)=>textRow(line,88,(notes.length>3?476:488)+i*(notes.length>3?40:56),noteSize,'#eee9d5'));
  return rows;
}
