import clues from '../cloudflare/clues.mjs';
export function verifiedProgress(boards){
 if(!boards||typeof boards!=='object'||Array.isArray(boards))return 0;
 const keys=Object.keys(boards);if(!keys.length||keys.some(k=>!['2','3','4','5','6','7','8','9'].includes(k)))return 0;
 const highest=Math.max(...keys.map(Number));
 for(let n=2;n<=highest;n++){
  const v=boards[n];if(!Array.isArray(v)||v.length!==n*n||v.some((x,i)=>!Number.isInteger(x)||x<1||x>n||(clues[n][i]&&clues[n][i]!==x)))return 0;
  for(let a=0;a<n;a++)if(new Set(v.slice(a*n,(a+1)*n)).size!==n||new Set(Array.from({length:n},(_,b)=>v[b*n+a])).size!==n)return 0;
  const at=(a,b)=>v[(a-1)*n+b-1];for(let a=1;a<=n;a++)for(let b=1;b<=n;b++)for(let c=1;c<=n;c++)if(at(at(a,b),c)!==at(a,at(b,c)))return 0;
 }
 return highest-1;
}
export const levelOf=r=>r.completedLevels??8;
export const reachedAt=r=>r.reached_at||r.first_at;
export function ranked(rows){return rows.sort((a,b)=>levelOf(b)-levelOf(a)||reachedAt(a).localeCompare(reachedAt(b))||a.id.localeCompare(b.id));}
export function publicRecord(r,full=false){
 const guest=r.kind==='guest';return {kind:guest?'guest':'student',studentId:guest?'':full?r.id:r.id.slice(0,3)+'****'+r.id.slice(-4),name:guest?'游客 '+r.name:full?r.name:r.initials,firstCompletedAt:r.first_at,updatedAt:r.updated_at,reachedAt:reachedAt(r),completedLevels:levelOf(r),highestLevel:levelOf(r)+1};
}
