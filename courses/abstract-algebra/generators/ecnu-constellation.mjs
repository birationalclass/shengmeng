// ECNU seal already used by the course's campus model; sample its ink into stars.
// Official reference: https://www.ecnu.edu.cn/wzcd/xxgk/xxbs.htm
export function mountEcnuConstellation(){
 const canvas=document.createElement('canvas');canvas.id='ecnuConstellation';
 canvas.setAttribute('aria-hidden','true');canvas.width=640;canvas.height=648;
 document.getElementById('cosmos').append(canvas);
 const image=new Image();
 image.onload=()=>{
  const mask=document.createElement('canvas');mask.width=320;mask.height=324;
  const m=mask.getContext('2d',{willReadFrequently:true});m.drawImage(image,0,0,320,324);
  const pixels=m.getImageData(0,0,320,324).data;
  const ink=(x,y)=>{if(x<0||y<0||x>=320||y>=324)return false;const i=(Math.floor(y)*320+Math.floor(x))*4;return pixels[i+3]>100&&pixels[i+1]<140&&pixels[i]>pixels[i+1]*1.5;};
  const c=canvas.getContext('2d');let seed=1951;
  const random=()=>{seed=seed*16807%2147483647;return(seed-1)/2147483646;};
  c.scale(2,2);c.lineWidth=.3;c.strokeStyle='rgba(149,195,240,.28)';
  for(let y=2;y<324;y+=3)for(let x=2;x<320;x+=3){
   if(!ink(x,y))continue;
   const px=x+(random()-.5)*2,py=y+(random()-.5)*2,bright=random(),radius=bright>.98?1.15:.22+random()*.43;
   if(ink(x+3,y)&&ink(x+1,y)){c.beginPath();c.moveTo(px,py);c.lineTo(x+3,y);c.stroke();}
   if(bright>.98){c.shadowColor='#aacfff';c.shadowBlur=7;}else c.shadowBlur=0;
   c.fillStyle=bright>.9?'rgba(235,229,209,.92)':`rgba(153,195,242,${.38+bright*.4})`;
   c.beginPath();c.arc(px,py,radius,0,Math.PI*2);c.fill();
  }
  c.shadowBlur=0;canvas.classList.add('ready');
 };
 image.src=new URL('../../../visuals/group-sudoku/images/ecnu-seal.png',import.meta.url).href;
 return canvas;
}
