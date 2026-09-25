import {FIELD} from './elliptic-model.js';
// Navigation uses metres and a persistent position, independent of look angles.
export function motion(yaw,forward,right,up,metres){
 const length=Math.max(1,Math.hypot(forward,right,up));
 return {x:(Math.cos(yaw)*forward-Math.sin(yaw)*right)*metres/length,
  z:(Math.sin(yaw)*forward+Math.cos(yaw)*right)*metres/length,
  height:up*metres/length};
}
export function distanceSampler(image){
 const canvas=document.createElement('canvas');canvas.width=image.width;canvas.height=image.height;
 const context=canvas.getContext('2d',{willReadFrequently:true});context.drawImage(image,0,0);
 const {data}=context.getImageData(0,0,image.width,image.height),width=image.width,height=image.height;
 const at=(x,y)=>(data[(y*width+x)*4]*256+data[(y*width+x)*4+1])*.01;
 return (x,z)=>{
  const u=(x-FIELD.minX)/FIELD.size*width-.5,v=(z-FIELD.minZ)/FIELD.size*height-.5;
  if(u<0||u>=width-1||v<0||v>=height-1)return 400;
  const i=Math.floor(u),j=Math.floor(v),a=u-i,b=v-j;
  return (1-b)*((1-a)*at(i,j)+a*at(i+1,j))+b*((1-a)*at(i,j+1)+a*at(i+1,j+1));
 };
}
