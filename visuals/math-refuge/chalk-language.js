import {orbitDiagram} from './orbit-diagram.js';
import {inlineInk,drawInlineInk} from './chalk-inline-math.js?v=inline-formula-2';
import {chalkInlineRuns,mathFont} from './chalk-typography.js?v=inline-root-1';
import {drawChalkAnnotation} from './chalk-annotations.js?v=report-line-sync-6';
import {explainedFlow} from './flow-explanation.js?v=textbook-problems-1';
import {wrapBoardText} from './chalk-wrap.js?v62-chalk-ink';
import {classroomHeading,CHALK_SEMANTIC_COLORS,drawReferenceIcon} from './classroom-metadata.js?v=sylow-two-lessons-20261015';
import {focusPieces} from './chalk-blue-focus.js';
export function chalkCopy(page,language='zh',{board=false}={}){
  return language==='en'?{...page.en,text:!board&&page.en.readingText||page.en.text}:{title:page.title,text:!board&&page.readingText||page.text,source:page.source,author:page.author};
}
export function chalkPageText(page,language='zh'){
 const copy=chalkCopy(page,language,{board:true}),pick=value=>Array.isArray(value)?value[language==='en'?1:0]:value;
 return [copy.source,copy.title,copy.author,page.presenter,page.assistant,page.assistantEn,copy.text,...(page.exerciseLines||[]).map(l=>language==='en'?l.enText:l.text),pick(page.topic),pick(page.subtitle),...(page.boardLines||[]).map(l=>l.tex||(language==='en'?l.enText:l.text)),...(page.flowLabels||[]).map(l=>language==='en'?l.enText:l.text),JSON.stringify(page.annotation||{}),JSON.stringify(page.diagram||{}),JSON.stringify(page.arrowReasons||{})].filter(Boolean).join('\n');
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
  function textRow(text,x,y,size,color,heading=false,mark=null){
    while(measure(text,size,heading)>1368&&size>24)size--;
    ctx.fillStyle=color;let cursor=x;const chineseSpans=[];
    const proseFocus=mark?.textFragments?.[language]||[];
    for(const original of chalkInlineRuns(text))for(const piece of original.math?[{text:original.text,blue:mark?.fragments?.some(part=>original.text.includes(part))}]:focusPieces(original.text,proseFocus)){const run={...original,text:piece.text,mathStyle:options.mathStyle||'mali-italic'};ctx.fillStyle=piece.blue?'#93c9ff':color;ctx.font=`${size*(run.script ? .7 : 1)}px ${runFont(run,heading)}`;drawInlineInk(ctx,run,cursor,y+(run.script==='sub'?size*.22:run.script==='sup'?-size*.4:0),size*(run.script?.7:1));const width=inlineInk(ctx,run,size*(run.script?.7:1)).width;if(/[\u3400-\u9fff]/.test(run.text))chineseSpans.push([cursor,cursor+width]);cursor+=width;}
    const ink=bounds(text,size,heading);
    rows.push(Object.assign([x+ink.left-4,y-ink.ascent-4,ink.right-ink.left+8,ink.ascent+ink.descent+8],{chineseSpans,chalkColor:color}));
  }
  if(page.kind==='closing'){let size=124;while(measure(copy.title,size)>1368&&size>24)size--;textRow(copy.title,(1536-measure(copy.title,size))/2,360,size,'#e4cf9c',false,page.emphasis?.[0]);return rows;}
  if(page.kind==='cover'){
    const center=(text,y,size,color='#eee9d5')=>{while(measure(text,size)>1368&&size>24)size--;textRow(text,(1536-measure(text,size))/2,y,size,color);};
    if(page.period==='break'){center(language==='en'?'Break':'课间休息',220,106,'#e4cf9c');return rows;}
    if(page.coverType==='section'){center(copy.title,190,106,'#e4cf9c');center(language==='en'?page.presenterEn:page.presenter,320,48);center(language==='en'?page.assistantEn:page.assistant,405,48);center(copy.text,535,38,'#e4cf9c');return rows;}
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
  if(!page.hideHeading&&!options.hideHeading){const icon=page.classroom&&page.reference?.kind;ctx.fillStyle='#e4cf9c';if(icon)drawReferenceIcon(ctx,icon,84,38,36);textRow(page.classroom?classroomHeading(page,language,copy.title):copy.source+'  '+copy.title,icon?136:84,76,44,'#e4cf9c',true);rows.at(-1).mainLine=0;if(icon){const r=rows.at(-1),right=r[0]+r[2],bottom=r[1]+r[3];r[0]=80;r[1]=Math.min(36,r[1]);r[2]=right-80;r[3]=Math.max(76,bottom)-r[1];}}
  if(page.exerciseBoard||page.statementBoard||page.expositionBoard){
    if(page.exerciseLines.length>5)throw Error('Exercise needs another physical board: '+page.title);
    page.exerciseLines.forEach((line,i)=>{if(line.tex){ctx.drawImage(formula,88,158+i*83-60,1360,142);rows.push(Object.assign([88,158+i*83-60,1360,142],{mainLine:i+1,formulaRow:0}));return;}const text=language==='en'?line.enText:line.text,mark=page.emphasis?.[i+1];let size=38;const width=page.orbitVisualization?865:page.exerciseBoard?1000:1328;while(measure(text,size)>width&&size>28)size--;if(measure(text,size)>width)throw Error('Exercise line overflows: '+text);textRow(text,88,158+i*83,size,CHALK_SEMANTIC_COLORS[mark?.tone]||'#eee9d5',false,mark);rows.at(-1).mainLine=i+1;
      if(page.orbitVisualization&&i===1){orbitDiagram(ctx,{
       stroke(points,color,width){ctx.save();ctx.strokeStyle=color;ctx.lineWidth=width;ctx.lineCap='round';ctx.lineJoin='round';ctx.beginPath();points.forEach(([x,y],j)=>j?ctx.lineTo(x,y):ctx.moveTo(x,y));ctx.stroke();ctx.restore();const xs=points.map(p=>p[0]),ys=points.map(p=>p[1]);rows.push(Object.assign([Math.min(...xs)-width,Math.min(...ys)-width,Math.max(...xs)-Math.min(...xs)+2*width,Math.max(...ys)-Math.min(...ys)+2*width],{strokePath:points,strokeWidth:width,chalkColor:color,mainLine:2,auxiliaryDiagram:true}));},
       label(text,x,y,size,color){textRow(text,x,y,size,color);rows.at(-1).mainLine=2;rows.at(-1).auxiliaryDiagram=true;}
      });}
    });
    return rows;
  }
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
        const reason=page.arrowReasons?.[item.mainLine];
        if(reason){const arrow=formula.authoredOperations?.find(o=>['⇒','⟹','→'].includes(o.symbol)&&o.rect[0]+o.rect[2]/2>=source[0]&&o.rect[0]+o.rect[2]/2<=source[0]+source[2]&&o.rect[1]+o.rect[3]/2>=source[1]&&o.rect[1]+o.rect[3]/2<=source[1]+source[3]);if(!arrow)throw Error('Reason needs a visible implication arrow: '+page.title);const a=arrow.symbolRect||arrow.rect,x=item.rect[0]+(a[0]+a[2]/2-source[0])/source[2]*item.rect[2],label=reason[language],size=24;textRow(label,x-measure(label,size)/2,item.rect[1]+2,size,'#eee9d5');rows.at(-1).mainLine=item.mainLine;rows.at(-1).proofReason=true;}

        if(item.index===cues.afterRow)rows.push(...cues.map(c=>Object.assign(c,{mainLine:item.mainLine})));
      }else{
        textRow(item.text,item.x,item.y,item.size,CHALK_SEMANTIC_COLORS[page.emphasis?.[item.mainLine]?.tone]||'#eee9d5',false,page.emphasis?.[item.mainLine]);
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
