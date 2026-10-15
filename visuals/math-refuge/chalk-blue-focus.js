// Split prose only. Mathematical runs retain the display-math atlas geometry.
export function focusPieces(text,fragments=[]){
 const ranges=[];for(const fragment of fragments){let at=0;while(fragment&&(at=text.indexOf(fragment,at))>=0){ranges.push([at,at+fragment.length]);at+=fragment.length;}}
 const points=[...new Set([0,text.length,...ranges.flat()])].sort((a,b)=>a-b),pieces=[];
 for(let i=1;i<points.length;i++){const a=points[i-1],b=points[i];if(b>a)pieces.push({text:text.slice(a,b),blue:ranges.some(([x,y])=>a>=x&&b<=y)});}return pieces;
}
