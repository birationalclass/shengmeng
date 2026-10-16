import {resourceFetch} from './resource-fetch.js';
// Device limits are fixed for the visit, including landscape/iPad orientations.
export function mobilePolicy({width=1280,height=800,userAgent='',maxTouchPoints=0,coarsePointer=false,safe=false}={}){
 const ios=/iPad|iPhone|iPod/.test(userAgent)||(/Macintosh/.test(userAgent)&&maxTouchPoints>1);
 const mobile=ios||/Android|Mobile/.test(userAgent)||(coarsePointer&&Math.min(width,height)<=1024);
 const compact=mobile||safe;
 return {mobile:compact,ios,safe,boardScale:compact?.5:1,
  cloudSize:compact?256:512,cloudSteps:compact?16:24,cloudInterval:compact?500:250,
  noiseSize:compact?32:64,atmosphereSize:compact?128:256,atmosphereInterval:compact?1000:250};
}
export function withDeadline(promise,ms,label){
 let timer;return Promise.race([promise,new Promise((_,reject)=>{timer=setTimeout(()=>reject(new Error(label+'超时，请检查网络后重试。')),ms);})]).finally(()=>clearTimeout(timer));
}
export async function fetchLocal(url,{timeout=15000,...options}={}){
 try{const response=await resourceFetch(url,{...options,resourceIdleTimeout:timeout});if(!response.ok)throw new Error('资源加载失败：'+response.status);return await response.text();}
 catch(error){if(error.name==='TimeoutError')throw new Error('资源加载超时，请检查网络后重试。',{cause:error});throw error;}
}
export function decodeImage(url,timeout=20000){
 if(typeof location!=='undefined'&&!/^(blob:|data:)/.test(String(url))){return resourceFetch(url).then(r=>{if(!r.ok)throw Error('图像加载失败：'+r.status);return r.blob();}).then(async blob=>{const src=URL.createObjectURL(blob);try{return await decodeImage(src,timeout);}finally{URL.revokeObjectURL(src);}});}
 return new Promise((resolve,reject)=>{const image=new Image(),timer=setTimeout(()=>{image.onload=image.onerror=null;image.src='';reject(new Error('图像加载超时，请检查网络后重试。'));},timeout);
 image.onload=()=>{clearTimeout(timer);resolve(image);};image.onerror=()=>{clearTimeout(timer);reject(new Error('图像加载失败，请检查网络后重试。'));};image.src=url;});
}
