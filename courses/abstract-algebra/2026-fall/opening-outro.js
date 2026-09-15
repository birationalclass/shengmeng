/* One geometry per language, sampled only after the required fonts are ready. */
(()=>{
  'use strict';
  const cache=new Map();
  function titleInk(en){
    if(!document.fonts.check('180px CourseCalligraphy','代数学孟晟'))throw new Error('The course calligraphy font is not ready');
    const canvas=document.createElement('canvas');canvas.width=1600;canvas.height=800;const ctx=canvas.getContext('2d',{willReadFrequently:true});
    ctx.fillStyle='#fff';ctx.textAlign='left';
    const title=en?'Algebra':'代数学',font=en?'200px OpeningSerif,Georgia,serif':'220px CourseCalligraphy';
    ctx.font=font;const tw=ctx.measureText(title).width;ctx.font='200px OpeningSerif,Georgia,serif';const rw=ctx.measureText('Ⅰ').width,gap=42,start=(1600-tw-gap-rw)/2;
    ctx.font=font;ctx.fillText(title,start,365);ctx.font='200px OpeningSerif,Georgia,serif';ctx.fillText('Ⅰ',start+tw+gap,365);
    ctx.textAlign='center';ctx.font=en?'106px OpeningCopperplate,serif':'106px CourseCalligraphy';ctx.fillText(en?'Sheng Meng':'孟晟',800,590);
    const data=ctx.getImageData(0,0,1600,800).data,ink=[];for(let i=0;i<1600*800;i++)if(data[i*4+3]>72)ink.push(i);return ink;
  }
  function create(count){
    const en=window.CourseLanguage?.language==='en',key=(en?'en':'zh')+count;if(cache.has(key))return cache.get(key);
    const ink=titleInk(en);
    let seed=137;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};const points=[];
    for(let i=0;i<count;i++){const pixel=ink[Math.floor(random()*ink.length)],x=((pixel%1600)+random()-800)/640,y=(400-Math.floor(pixel/1600)-random())/640;points.push([x,y,(random()-.5)*.004,Math.floor(pixel/1600)>470?1:0]);}
    points.sort((a,b)=>Math.atan2(a[1],a[0])-Math.atan2(b[1],b[0])||Math.hypot(a[0],a[1])-Math.hypot(b[0],b[1]));
    const positions=new Float32Array(count*3),normals=new Float32Array(count*3),signatureWeights=new Float32Array(count);
    points.forEach((point,i)=>{positions[i*3]=point[0];positions[i*3+1]=point[1];positions[i*3+2]=point[2];normals[i*3+2]=1;signatureWeights[i]=point[3];});
    const value={positions,normals,signatureWeights,language:en?'en':'zh'};cache.set(key,value);return value;
  }
  window.CourseOpeningOutro=Object.freeze({create});
})();
