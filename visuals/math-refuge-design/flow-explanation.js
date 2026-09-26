import {conciseEnglish} from './board-explanations.js?v62-chalk-ink';
import {wrapBoardText} from './chalk-wrap.js?v62-chalk-ink';
// Aim for six to eight measured lines, using the full writable height.
export function explainedFlow(page,language,measure,hideHeading=false){
  const paragraphs=(language==='en'&&conciseEnglish.get(page.title))||(language==='en'?page.en.text:page.text).split(/\n\s*\n/);
  const labels=page.flowLabels||[{y:-1,text:page.title,enText:page.en.title}];
  const blocks=labels.map((label,i)=>({
    cue:language==='en'?label.enText:label.text,explanation:page.proof?'':paragraphs[i]||'',
    formulas:page.formulaRows.map((source,index)=>({source,index})).filter(({source})=>source[1]>label.y&&source[1]<(labels[i+1]?.y??640))
  }));
  const start=page.hideHeading||hideHeading?38:112,bottom=606,available=bottom-start;
  const wrapped=new Map();
  function wrap(text,size,width,breakClauses){
    const key=size+':'+width+':'+breakClauses+':'+text;if(wrapped.has(key))return wrapped.get(key);
    const lines=wrapBoardText(text,size,width,measure,breakClauses);wrapped.set(key,lines);return lines;
  }
  let best;
  for(const size of [46,44,42,40,38,36,34,32,30,28,26])for(const width of page.boardLines?[1328]:[1328,1200,1080,960,840,760])for(const breakClauses of page.boardLines?[false]:[true,false]){
    for(const requestedScale of [1.5,1.3,1.15,1,.85,.7,.65]){
      const items=[];
      const text=(value,role)=>{for(const line of wrap(value,size,width,breakClauses)){
        const ink=measure.bounds?.(line,size)||{ascent:size,descent:12};
        items.push({text:line,role,size,ascent:ink.ascent,height:Math.max(size+20,ink.ascent+ink.descent+8)});
      }};
      const formula=(source,index)=>{const scale=Math.min(requestedScale,1328/source[2]);items.push({source,index,width:source[2]*scale,height:source[3]*scale});};
      if(page.boardLines){
        let index=0;
        for(const line of page.boardLines){if(line.tex){formula(page.formulaRows[index],index);index++;}else text(language==='en'?line.enText:line.text,'explanation');}
      }else for(const b of blocks){
        if(!b.explanation)text(b.cue,'cue');
        for(const {source,index} of b.formulas){
          formula(source,index);
        }
        if(b.explanation)text(b.explanation,'explanation');
      }
      const ink=items.reduce((sum,i)=>sum+i.height,0),count=items.length;
      if(ink+Math.max(0,count-1)*(page.annotation?16:6)>available)continue;
      const totalLines=count+(page.hideHeading||hideHeading?0:1);
      const linePenalty=totalLines<6?(6-totalLines)*150:totalLines>8?(totalLines-8)*100:0;
      const shortTails=items.filter(i=>i.text&&i.role==='explanation'&&measure(i.text,size)<size*5).length;
      const score=linePenalty+shortTails*240+Math.abs(size-40)*2+(1328-width)/65+Math.abs(requestedScale-1.15)*12;
      if(!best||score<best.score)best={items,ink,score};
    }
  }
  if(!best)throw new Error('Board needs another page: '+page.title+' ('+language+')');
  const gap=best.items.length>1?(available-best.ink)/(best.items.length-1):0;let y=start;
  return best.items.map(item=>{
    const result=item.source?{...item,rect:[112,y,item.width,item.height]}:{...item,x:88,y:y+item.ascent+4};
    y+=item.height+gap;return result;
  });
}
