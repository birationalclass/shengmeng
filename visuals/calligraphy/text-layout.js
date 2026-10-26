export const homepageQuote='天之道损有余而补不足';
// The homepage uses equal em boxes, right-to-left columns, a .14em column
// gap and a .43em optical drop between the two column starts.
export function textPlacements(count,layout='auto'){
 if(layout==='homepage'){
  const first=Math.min(3,count),pitch=3.18;
  return Array.from({length:count},(_,i)=>({x:(i<first?.5:-.5)*1.14*pitch,y:-(i<first?i:i-first+.43)*pitch,cell:pitch}));
 }
 const columns=Math.min(4,count),rows=Math.ceil(count/columns);
 return Array.from({length:count},(_,i)=>{const row=Math.floor(i/columns),col=i%columns,rowCount=Math.min(columns,count-row*columns);return {x:(col-(rowCount-1)/2)*3.46,y:((rows-1)/2-row)*3.65,cell:3.18};});
}
