// The interactive world and its optional rooms have separate readiness gates.
export function waitForEntered(node,target=window){
 if(node.dataset.entered==='true')return Promise.resolve();
 return new Promise(resolve=>{const check=()=>{if(node.dataset.entered!=='true')return;target.removeEventListener('refuge-entered',check);resolve();};target.addEventListener('refuge-entered',check);check();});
}
export function idleTurn(api=globalThis){return new Promise(resolve=>{if(api.requestIdleCallback)api.requestIdleCallback(resolve,{timeout:750});else api.setTimeout(resolve,32);});}
export function loadBoardFonts(doc=document){return doc.fonts?Promise.all(['42px RefugeChinese','42px RefugeLatin','42px RefugeMath'].map(font=>doc.fonts.load(font))):Promise.resolve();}
export async function loadMathRuntime(){
 if(window.katex)return;
 const base=new URL('../../study/spectral/vendor/',import.meta.url),css=document.createElement('link');css.rel='stylesheet';css.href=new URL('katex.min.css',base).href;document.head.append(css);
 await new Promise((resolve,reject)=>{const script=document.createElement('script');script.src=new URL('katex.min.js',base).href;script.onload=resolve;script.onerror=()=>reject(new Error('数学排版工具加载失败'));document.head.append(script);});
}
