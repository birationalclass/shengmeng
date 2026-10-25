// The physical board order and the actual audio order are shown separately.
export function renderClassroomManuscript(container,board,manifest,index){
 const doc=container.ownerDocument,append=(tag,text,className)=>{const el=doc.createElement(tag);el.textContent=text;if(className)el.className=className;container.append(el);return el;};
 const stamp=t=>{const n=Math.round(t*10);return `${Math.floor(n/600).toString().padStart(2,'0')}:${((n%600)/10).toFixed(1).padStart(4,'0')}`;};
 container.replaceChildren();append('h3','板面文字（书写顺序）');
 for(const row of board.rows)append('p',row.id+' · '+row.display);
 const item=manifest?.boards[index];if(!item){append('p','语音目录尚未就绪，当前只显示板面文字。');return;}
 append('h3','口播（实际播放顺序）');
 if(board.difficultyLabel)append('p',`难度：${board.difficultyLabel}；${board.difficultyReason}。`);
 const speech=manifest.paragraphs.filter(p=>p.page===index).map(p=>({...p,start:p.start-item.start,end:p.end-item.start}));
 const waits=(item.waits||[]).map(w=>({...w,wait:true}));
 const pauses=(item.manualPauses||[]).map(p=>({start:p.at,end:p.at,manualPause:true}));
 for(const part of [...speech,...waits,...pauses].sort((a,b)=>a.start-b.start)){
  if(part.manualPause){append('p',`${stamp(part.start)} · 自动暂停板书和口播，交由小孟；手动播放后继续，不另计10秒。`,'wait');continue;}
  if(part.wait){append('p',`${stamp(part.start)}–${stamp(part.end)} · ${part.exercise?'独立思考':'思考'}${part.seconds}秒；结束前不显示下一答案行。`,'wait');continue;}
  const article=append('article','');article.dataset.line=part.lineId||'';article.dataset.start=part.start;article.dataset.end=part.end;
  const code=doc.createElement('code');code.textContent=`${stamp(part.start)}–${stamp(part.end)} · ${part.role==='question'?'旁白提问':part.lineId||'口播'}`;
  const text=doc.createElement('p');text.className='speech';text.textContent='口播：'+part.text;article.append(code,text);
  if(part.pronunciationHints?.length){const hint=doc.createElement('small');hint.className='pronunciation';hint.textContent='读音：'+[...new Map(part.pronunciationHints.map(h=>[h.term,h.term+'（'+h.pinyin+'）'])).values()].join('；');article.append(hint);}
 }
 if(board.kind==='break')append('p','课间休息：05:00。','wait');
 if(board.diagramAsset){const link=doc.createElement('a');link.href=board.diagramAsset;link.target='_blank';link.rel='noopener';link.textContent='查看图示数据';container.append(link);}
}
