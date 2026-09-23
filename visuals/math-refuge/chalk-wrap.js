const words=new Intl.Segmenter('zh',{granularity:'word'});
const closes=/^[，。；：！？、）】》,.!?;:)\]]/;
const opens=/[（【《(\[]$/;
const terms=['一般型','极小三维簇','典范映射','典范次数','典范体积','几何亏格','极小模型','超对称','分数费米数','边界条件','表示范畴','张量范畴','链复形','上链复形','谱序列','过滤复形','同调群','上同调群','双复形','微分映射','收敛性','商空间','不定点','有理分量','有效除子','标准除子','极端射线','纤维空间','底曲线','解析空间','代数曲面','代数三维簇','有限维','非正则曲面','正则曲面','双有理','半正定','正定性'];
const protectedTerms=new RegExp('('+terms.sort((a,b)=>b.length-a.length).join('|')+')','g');
const termSet=new Set(terms);
// Keep words, numbers and inline mathematical notation intact.
export function wrapBoardText(text,size,width,measure,breakClauses=false){
  const tokens=(text.match(/[A-Za-z0-9][A-Za-z0-9_^().{}+\-/]*|[\u3400-\u9fff]+|\s+|[^\s]/gu)||[])
    .flatMap(token=>/[\u3400-\u9fff]/.test(token)?token.split(protectedTerms).filter(Boolean).flatMap(part=>termSet.has(part)?[part]:[...words.segment(part)].map(word=>word.segment)):[token]);
  const clauses=[[]];
  for(const token of tokens){clauses.at(-1).push(token);if(breakClauses&&/[。；：!?]$/.test(token))clauses.push([]);}
  const result=[];
  const ink=parts=>measure(parts.join('').trim(),size);
  for(const clause of clauses){
    const lines=[[]];
    for(const token of clause){
      const current=lines.at(-1);
      if(current.length&&ink([...current,token])>width&&!closes.test(token)&&!opens.test(current.join('').trimEnd()))lines.push([token]);
      else current.push(token);
    }
    // Rebalance a short tail across the last two lines, always at a word boundary.
    if(lines.length>1&&ink(lines.at(-1))<width*.55){
      const pair=lines.at(-2).concat(lines.at(-1));let best;
      for(let i=1;i<pair.length;i++){
        const a=pair.slice(0,i),b=pair.slice(i),left=a.join('').trim(),right=b.join('').trim();
        if(!left||!right||closes.test(right)||opens.test(left))continue;
        const wa=ink(a),wb=ink(b);if(wa>width||wb>width)continue;
        const score=Math.abs(wa-wb)-( /[，,；;：:]$/.test(left)?size*2:0 );
        if(!best||score<best.score)best={a,b,score};
      }
      if(best)lines.splice(-2,2,best.a,best.b);
    }
    result.push(...lines.map(line=>line.join('').trim()).filter(Boolean));
  }
  return result;
}
