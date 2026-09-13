/* A historical portrait, group name and life dates, all rendered as grains. */
(() => {
  'use strict';
  const countParts=[.68,.25,.07];
  function textPixels(text,font){
    const c=document.createElement('canvas');c.width=1600;c.height=260;
    const ctx=c.getContext('2d',{willReadFrequently:true});ctx.fillStyle='#fff';ctx.textAlign='center';ctx.textBaseline='middle';ctx.font=font;ctx.fillText(text,800,130,1450);
    const pixels=ctx.getImageData(0,0,1600,260).data,ink=[];
    for(let y=0;y<260;y++)for(let x=0;x<1600;x++)if(pixels[(y*1600+x)*4+3]>150)ink.push([x,y]);
    if(!ink.length)throw new Error('Galois lettering could not be prepared');return ink;
  }
  function sample(count){
    const binary=atob(window.CourseOpeningGaloisPortrait),bytes=Uint8Array.from(binary,c=>c.charCodeAt(0)),view=new DataView(bytes.buffer),portraitCount=bytes.length/4;
    const title=textPixels('Galois Group','400 190px Georgia, "Times New Roman", serif');
    const dates=textPixels('1811–1832','400 100px Georgia, "Times New Roman", serif');
    let seed=18111832;const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
    const points=[],componentCounts=[0,0,0];
    for(let i=0;i<count;i++){
      let x,y,id;
      if(i<count*countParts[0]){
        id=0;const j=Math.floor(random()*portraitCount)*4;
        x=(view.getUint16(j,true)/65535-.5)*.94+(random()-.5)*.0015;
        y=.97-view.getUint16(j+2,true)/65535*1.28+(random()-.5)*.0015;
      }else{
        id=i<count*(countParts[0]+countParts[1])?1:2;
        const ink=id===1?title:dates,p=ink[Math.floor(random()*ink.length)],scale=id===1?740:930;
        x=(p[0]+random()-800)/scale;y=(130-p[1]-random())/scale+(id===1?-.46:-.69);
      }
      points.push([x,y,(random()-.5)*.004]);componentCounts[id]++;
    }
    points.sort((a,b)=>Math.atan2(a[1],a[0])-Math.atan2(b[1],b[0])||Math.hypot(a[0],a[1])-Math.hypot(b[0],b[1]));
    const positions=new Float32Array(count*3),normals=new Float32Array(count*3),flat=new Float32Array(count*2);
    points.forEach((p,i)=>{positions.set(p,i*3);normals[i*3+2]=1;flat.set(p.slice(0,2),i*2);});
    return {positions,normals,flat,componentCounts};
  }
  window.CourseOpeningGalois=Object.freeze({sample,evidence:()=>({name:'Évariste Galois',born:1811,died:1832,inscription:'Galois Group',dates:'1811–1832',portraitArtist:'Alfred Galois',portraitPublished:1848})});
})();
