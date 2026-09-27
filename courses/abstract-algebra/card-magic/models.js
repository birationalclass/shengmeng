/* Pure permutations. A deck is listed from top to bottom; labels never change. */
export const suits=['♣','♦','♥','♠'];
export const ranks=['A','2','3','4','5','6','7','8','9','10','J','Q','K'];
export const name=id=>suits[id%4]+ranks[Math.floor(id/4)];
export const rank=id=>Math.floor(id/4)+1;
export const codes=['LMH','LHM','MLH','MHL','HLM','HML'];
export function outShuffle(deck){if(deck.length%2)throw Error('Even deck required');const m=deck.length/2;return Array.from({length:deck.length},(_,i)=>deck[(i%2?m:0)+Math.floor(i/2)]);}
export function inShuffle(deck){if(deck.length%2)throw Error('Even deck required');const m=deck.length/2;return Array.from({length:deck.length},(_,i)=>deck[(i%2?0:m)+Math.floor(i/2)]);}
export function encodeFive(hand){
 if(hand.length!==5||new Set(hand).size!==5||hand.some(x=>!Number.isInteger(x)||x<0||x>51))throw Error('Choose five distinct cards');
 for(let i=0;i<5;i++)for(let j=i+1;j<5;j++)if(hand[i]%4===hand[j]%4){
  let base=hand[i],hidden=hand[j],distance=(rank(hidden)-rank(base)+13)%13;
  if(distance>6){[base,hidden]=[hidden,base];distance=13-distance;}
  const sorted=hand.filter(x=>x!==base&&x!==hidden).sort((a,b)=>a-b),code=codes[distance-1];
  return {base,hidden,distance,code,sorted,shown:[base,...[...code].map(letter=>sorted['LMH'.indexOf(letter)])]};
 }
}
export function decodeFour(shown){
 const sorted=shown.slice(1).sort((a,b)=>a-b),code=shown.slice(1).map(x=>'LMH'[sorted.indexOf(x)]).join(''),distance=codes.indexOf(code)+1;
 if(!distance)throw Error('Invalid code');return ((rank(shown[0])-1+distance)%13)*4+shown[0]%4;
}
export function targetRoute(position){
 if(!Number.isInteger(position)||position<1||position>52)throw Error('Use positions 1–52');
 const target=position-1,bits=target?target.toString(2):'',steps=[...bits].map(bit=>bit==='1'?'I':'O'),indices=[0];
 for(const bit of bits)indices.push(2*indices.at(-1)+Number(bit));
 return {target,bits,steps,indices};
}
