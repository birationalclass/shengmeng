// The interactive world and its optional rooms have separate readiness gates.
// Required resource preparation has no authentication or click-to-enter gate.
export function createOpeningPreparation({node,prepareRoom,prepareGPU,now=()=>performance.now()}){
 let job=null;node.dataset.openingPreparation='pending';
 return function prepare(){
  if(job)return job;
  node.dataset.openingPreparation='loading';node.dataset.preparationStartedMs=String(now());
  job=Promise.resolve().then(prepareRoom).then(prepareGPU).then(()=>{
   node.dataset.openingPreparation='ready';node.dataset.openingPreparedMs=String(now());node.dataset.preparedBeforeEntry=String(node.dataset.entered!=='true');delete node.dataset.preparationError;
  }).catch(error=>{job=null;node.dataset.openingPreparation='error';node.dataset.preparationError=error.message;throw error;});
  return job;
 };
}
export function waitForEntered(node,target=window){
 if(node.dataset.entered==='true')return Promise.resolve();
 return new Promise(resolve=>{const check=()=>{if(node.dataset.entered!=='true')return;target.removeEventListener('refuge-entered',check);resolve();};target.addEventListener('refuge-entered',check);check();});
}
export function idleTurn(api=globalThis){return new Promise(resolve=>{if(api.requestIdleCallback)api.requestIdleCallback(resolve,{timeout:750});else api.setTimeout(resolve,32);});}
export function loadBoardFonts(doc=document){return doc.fonts?Promise.all(['42px RefugeChinese','42px RefugeLatin','42px RefugeMath','42px RefugeMathSymbols'].map(font=>doc.fonts.load(font))):Promise.resolve();}
export async function loadMathRuntime(){
 if(window.katex)return;
 const base=new URL('../../study/spectral/vendor/',import.meta.url),css=document.createElement('link');css.rel='stylesheet';css.href=new URL('katex.min.css',base).href;document.head.append(css);
 await new Promise((resolve,reject)=>{const script=document.createElement('script');script.src=new URL('katex.min.js',base).href;script.onload=resolve;script.onerror=()=>reject(new Error('数学排版工具加载失败'));document.head.append(script);});
}
