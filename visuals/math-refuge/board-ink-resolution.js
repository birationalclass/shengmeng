export function boardInkScale({base=1,width=1536,height=640,maxTextureSize=4096,previous=base}={}){
 if(base<1)return base;
 // Never shrink an allocated board when its neighbour becomes active.
 return Math.min(2,Math.max(previous,Math.ceil(Math.min(width/1536,height/640)*1.2)),maxTextureSize/1536);
}
