/* A two-line sand inscription, sampled once before the opening becomes ready. */
(() => {
  'use strict';
  window.CourseOpeningOutro={create(count){
    const canvas=document.createElement('canvas');canvas.width=1600;canvas.height=800;
    const ctx=canvas.getContext('2d',{willReadFrequently:true});
    ctx.fillStyle='#fff';ctx.textAlign='center';ctx.textBaseline='alphabetic';
    ctx.font='400 280px Georgia, "Times New Roman", serif';
    ctx.fillText('Algebra Ⅰ',800,390,1420);
    ctx.font='100 82px "Helvetica Neue", "Segoe UI", Arial, sans-serif';
    ctx.fillText('Sheng Meng',800,565,900);
    const pixels=ctx.getImageData(0,0,1600,800).data,ink=[];
    for(let y=0;y<800;y++)for(let x=0;x<1600;x++)if(pixels[(y*1600+x)*4+3]>150)ink.push(y*1600+x);
    if(!ink.length)throw new Error('The closing inscription could not be prepared');
    let seed=137;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
    const points=[];
    for(let i=0;i<count;i++){
      const pixel=ink[Math.floor(random()*ink.length)],x=((pixel%1600)+random()-800)/640,y=(400-Math.floor(pixel/1600)-random())/640;
      points.push([x,y,(random()-.5)*.004]);
    }
    // An angular ordering follows the same broad correspondence as the figures.
    points.sort((a,b)=>Math.atan2(a[1],a[0])-Math.atan2(b[1],b[0])||Math.hypot(a[0],a[1])-Math.hypot(b[0],b[1]));
    const positions=new Float32Array(count*3),normals=new Float32Array(count*3);
    points.forEach((point,i)=>{positions.set(point,i*3);normals[i*3+2]=1;});
    return{positions,normals};
  }};
})();
