const oldOrder=['C4','S3','V4','D4','Q8','S4','F56','A5','S5'];
export function migrateRecord(r,galaxies){const key=r.galaxyKey||oldOrder[r.highest],highest=galaxies.findIndex(g=>g.key===key);return {...r,galaxyKey:key,highest};}
export function completionRecord(account,journey,galaxies,previous,at=null){
 let highest=-1,completedLevels=0;
 for(const [i,g] of galaxies.entries()){const passed=journey[g.key]?.passed||0;if(passed){highest=i;completedLevels+=passed;}}
 if(highest<0)return previous||null;
 const advanced=!previous||highest>previous.highest||completedLevels>previous.completedLevels;
 return {...previous,id:account.id,kind:account.kind,name:account.name||'',initials:account.initials||previous?.initials||'',highest:Math.max(highest,previous?.highest??-1),galaxyKey:galaxies[Math.max(highest,previous?.highest??-1)]?.key,completedLevels:Math.max(completedLevels,previous?.completedLevels||0),reachedAt:advanced?at:previous.reachedAt};
}
export function publicRecord(r,full=false){return {...r,name:r.kind==='guest'?'游客 '+(r.name||r.id.replace(/^local-guest-|^guest_/, '').slice(0,8).toUpperCase()):full?r.name:(r.initials||'—'),studentId:r.kind==='guest'?'':full?r.id:r.id.slice(0,3)+'****'+r.id.slice(-4)};}
export function rankedRecords(records){return [...records].sort((a,b)=>b.highest-a.highest||String(a.reachedAt||'9999').localeCompare(String(b.reachedAt||'9999')));}

// Public rows mask student IDs. Only highlight a unique identity match.
export function ownRecordIndex(rows,account){
 if(!account?.id)return -1;
 const matches=[];
 rows.forEach((r,i)=>{
  if(r.kind!==account.kind)return;
  if(r.id){if(r.id===account.id)matches.push(i);return;}
  if(account.kind==='guest'){
   if(account.name&&r.name==='游客 '+account.name)matches.push(i);
  }else{
   const masked=account.id.slice(0,3)+'****'+account.id.slice(-4);
   if((r.studentId===account.id&&r.name===account.name)||(r.studentId===masked&&account.initials&&r.name===account.initials))matches.push(i);
  }
 });
 return matches.length===1?matches[0]:-1;
}

export function withOwnLocalRecord(cloudRows,local,account){
 const rows=cloudRows.map(r=>({...r}));if(!local)return rows;
 const index=ownRecordIndex(rows,account),remote=rows[index];
 if(!remote||local.highest>remote.highest||local.completedLevels>remote.completedLevels){
  const own={...publicRecord(local),localOnly:true};
  if(index<0)rows.push(own);else rows[index]={...own,consumedLives:Math.max(local.consumedLives||0,remote.consumedLives||0)};
 }
 return rankedRecords(rows);
}
