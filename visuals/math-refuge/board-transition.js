// Ordinary handwriting stays direct; only discontinuous content changes crossfade.
export function boardContentJump(previous,next){
 return Boolean(previous&&(previous.page!==next.page||previous.available!==next.available||Math.abs(previous.progress-next.progress)>.16));
}
export function boardFade(t){t=Math.max(0,Math.min(1,t));return t*t*(3-2*t);}

export function advanceBoardQueue(queue,dt,reduced=false){
 if(reduced){for(const board of queue){board.fadeAge=1;board.inkBlend.value=1;}queue.length=0;return;}
 if(!queue.length)return;
 const board=queue[0];board.fadeAge=Math.min(1,board.fadeAge+Math.max(0,Math.min(.1,dt))/.65);
 board.inkBlend.value=boardFade(board.fadeAge);if(board.fadeAge===1)queue.shift();
}
