// Device limits are fixed for the visit, including landscape/iPad orientations.
export function mobilePolicy({width=1280,height=800,userAgent='',maxTouchPoints=0,coarsePointer=false,safe=false}={}){
 const ios=/iPad|iPhone|iPod/.test(userAgent)||(/Macintosh/.test(userAgent)&&maxTouchPoints>1);
 const mobile=ios||/Android|Mobile/.test(userAgent)||(coarsePointer&&Math.min(width,height)<=1024);
 const compact=mobile||safe;
 return {mobile:compact,ios,safe,boardScale:compact?.5:1,
  cloudSize:compact?256:1024,cloudSteps:compact?16:32,cloudInterval:compact?500:100,
  noiseSize:compact?32:64,atmosphereSize:compact?128:256,atmosphereInterval:compact?1000:250};
}
export function withDeadline(promise,ms,label){
 let timer;return Promise.race([promise,new Promise((_,reject)=>{timer=setTimeout(()=>reject(new Error(label+'超时，请检查网络后重试。')),ms);})]).finally(()=>clearTimeout(timer));
}
export async function fetchLocal(url,{timeout=20000,...options}={}){
 const controller=new AbortController(),timer=setTimeout(()=>controller.abort(),timeout);
 try{const response=await fetch(url,{...options,signal:controller.signal});if(!response.ok)throw new Error('资源加载失败：'+response.status);return await response.text();}
 catch(error){if(controller.signal.aborted)throw new Error('资源加载超时，请检查网络后重试。');throw error;}
 finally{clearTimeout(timer);}
}
export function decodeImage(url,timeout=20000){
 return new Promise((resolve,reject)=>{const image=new Image(),timer=setTimeout(()=>{image.onload=image.onerror=null;image.src='';reject(new Error('图像加载超时，请检查网络后重试。'));},timeout);
 image.onload=()=>{clearTimeout(timer);resolve(image);};image.onerror=()=>{clearTimeout(timer);reject(new Error('图像加载失败，请检查网络后重试。'));};image.src=url;});
}
