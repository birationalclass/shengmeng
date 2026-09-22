// Deterministic modeled hardware and small reusable PBR texture maps.
export const TRAY={y:.305,z:-10.03,depth:.56,top:.335,restY:.400};
export function createBoardHardware(T){
  const maps=[],materials=[],geometries=[];
  function texture(w,h,paint,color=false){
    const bytes=new Uint8Array(w*h*4);
    for(let y=0;y<h;y++)for(let x=0;x<w;x++)bytes.set([...paint(x,y),255],(y*w+x)*4);
    const map=new T.DataTexture(bytes,w,h);map.needsUpdate=true;map.wrapS=map.wrapT=T.RepeatWrapping;
    map.generateMipmaps=true;map.minFilter=T.LinearMipmapLinearFilter;if(color)map.colorSpace=T.SRGBColorSpace;maps.push(map);return map;
  }
  const grain=(x,y)=>Math.sin(y*.72+Math.sin(x*.018)*2.5+Math.sin(x*.061+y*.023)*.6);
  const woodMap=texture(512,128,(x,y)=>{const g=grain(x,y),silk=Math.pow(Math.max(0,Math.sin(y*1.93+x*.006)),14)*20;return [130+g*13+silk,94+g*10+silk*.8,49+g*6+silk*.42].map(Math.round);},true);
  const woodBump=texture(512,128,(x,y)=>Array(3).fill(Math.round(126+grain(x,y)*15)));
  const feltMap=texture(128,128,(x,y)=>{const noise=((x*73+y*151+x*y*7)%71)/71,thread=Math.sin(x*2.7+y*.17)*Math.sin(y*1.9);return [43+noise*18+thread*4,49+noise*18+thread*4,43+noise*15+thread*4].map(Math.round);},true);
  const mat=options=>{const m=new T.MeshStandardMaterial(options);materials.push(m);return m;};
  const wood=mat({color:'#d6b778',map:woodMap,bumpMap:woodBump,bumpScale:.0015,roughness:.58,metalness:0,envMapIntensity:.16});wood.name='Golden-thread nanmu style';
  const back=mat({color:'#243c32',roughness:1,envMapIntensity:.04});back.name='Opaque chalkboard reverse';
  const felt=mat({color:'#b7b9a8',map:feltMap,bumpMap:feltMap,bumpScale:.0016,roughness:1,envMapIntensity:0});felt.name='Woven felt eraser pad';
  const rubber=mat({color:'#242b29',roughness:.95,envMapIntensity:0});
  function roundedBox(w,h,d,r=.018){
    r=Math.min(r,w/4,h/4);const x=-w/2,y=-h/2,s=new T.Shape();
    s.moveTo(x+r,y);s.lineTo(x+w-r,y);s.quadraticCurveTo(x+w,y,x+w,y+r);s.lineTo(x+w,y+h-r);s.quadraticCurveTo(x+w,y+h,x+w-r,y+h);s.lineTo(x+r,y+h);s.quadraticCurveTo(x,y+h,x,y+h-r);s.lineTo(x,y+r);s.quadraticCurveTo(x,y,x+r,y);
    const g=new T.ExtrudeGeometry(s,{depth:d-.008,bevelEnabled:true,bevelSize:.004,bevelThickness:.004,bevelSegments:2,steps:1,curveSegments:4});g.translate(0,0,-d/2+.004);geometries.push(g);return g;
  }
  return {wood,back,felt,rubber,roundedBox,dispose(){maps.forEach(m=>m.dispose());materials.forEach(m=>m.dispose());geometries.forEach(g=>g.dispose());}};
}
