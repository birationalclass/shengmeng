export function boardInkScale({base=1,width=1536,height=640,maxTextureSize=4096}={}){
 if(base<1)return base;
 return Math.min(2,Math.max(1,Math.ceil(Math.min(width/1536,height/640)*1.2)),maxTextureSize/1536);
}
