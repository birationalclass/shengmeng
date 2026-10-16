// Yield between small decode/layout steps; never stop background file downloads.
export function preparationTurn({background=true}={}){
 if(typeof window==='undefined')return Promise.resolve();
 return new Promise(resolve=>{if(background&&window.requestIdleCallback)window.requestIdleCallback(resolve,{timeout:500});else setTimeout(resolve,0);});
}
