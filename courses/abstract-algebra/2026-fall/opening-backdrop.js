/* Dark mathematical logos stay beneath the sand; captions are foreground DOM. */
(() => {
  'use strict';
  const scenes = [
    {logo:'D₆',title:'六瓣玫瑰',zh:'旋转六十度，花瓣重新重合。旋转与反射组成二面体群 D₆。',en:'Six petals. Rotations and reflections form the dihedral group D₆.'},
    {logo:'D₈',title:'八角星',zh:'八次旋转，八面镜像。十六个对称变换，在复合运算下组成群。',en:'Eight rotations and eight reflections: sixteen symmetries, one group.'},
    {logo:'D₁₂',title:'十二重花窗',zh:'每转三十度，花窗便与自身重合。对称把局部的重复连成整体。',en:'A thirty-degree turn brings the window back to itself.'},
    {logo:'E₈',title:'E₈ 根系',zh:'八维空间中的 240 个根投向平面；交织的线条留下高维对称的影子。',en:'240 roots in eight dimensions. A planar glimpse of exceptional symmetry.'},
    {logo:'ℂ',title:'Julia 分形',zh:'在复平面反复施行同一个映射。迭代的边界，蕴藏无尽的细节。',en:'Iteration in the complex plane reveals an endlessly intricate boundary.'},
    {logo:'ℤ',title:'THE LORD OF THE RING',zh:'整数环是含幺环的起点：到每个含幺环，都有唯一的保幺环同态。',en:'From ℤ to every unital ring, there is a unique unital homomorphism.',kind:'ring-verse',quote:'One Ring to rule them all,\nOne Ring to find them,\nOne Ring to bring them all,\nand in the darkness bind them.'},
    {logo:'Δ',title:'正多面体群',kind:'theorem',quote:'三角群\n定理　在三维欧氏空间中，凸正多面体按相似分类恰有五种：正四面体、正六面体、正八面体、正十二面体、正二十面体。\n\n保向球面三角群\nΔ⁺(2,3,3) ≅ A₄：四面体\nΔ⁺(2,3,4) ≅ S₄：六、八面体\nΔ⁺(2,3,5) ≅ A₅：十二、二十面体'}
  ];
  function create(gl) {
    const surface=document.createElement('canvas'),ctx=surface.getContext('2d');
    const texture=gl.createTexture();gl.bindTexture(gl.TEXTURE_2D,texture);
    gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.LINEAR);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MAG_FILTER,gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_S,gl.CLAMP_TO_EDGE);gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_T,gl.CLAMP_TO_EDGE);
    let key='',fontVersion=0;
    if(document.fonts){document.fonts.load('100px OpeningMath').then(()=>{fontVersion++;});document.fonts.ready.then(()=>{fontVersion++;});}
    return {
      update(index,width,height,ratio){
        const next=[index,width,height,ratio,fontVersion].join(':');if(next===key)return;key=next;
        surface.width=Math.round(width*ratio);surface.height=Math.round(height*ratio);ctx.setTransform(ratio,0,0,ratio,0,0);
        const scene=scenes[index],small=width<700;
        const size=Math.min(height*.74,width*.57);
        ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillStyle='rgba(175,153,112,.052)';ctx.font=`400 ${size}px OpeningMath, "STIX Two Math", Georgia, serif`;
        ctx.fillText(scene.logo,width*(small?.57:.60),height*.52,width*.75);
        gl.bindTexture(gl.TEXTURE_2D,texture);gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL,false);gl.texImage2D(gl.TEXTURE_2D,0,gl.RGBA,gl.RGBA,gl.UNSIGNED_BYTE,surface);
      },
      bind(){gl.activeTexture(gl.TEXTURE0);gl.bindTexture(gl.TEXTURE_2D,texture);},
      dispose(){gl.deleteTexture(texture);}
    };
  }
  window.CourseOpeningBackdrop={scenes,create,
    vertex:'attribute vec2 pos;varying vec2 uv;void main(){uv=vec2((pos.x+1.)*.5,(1.-pos.y)*.5);gl_Position=vec4(pos,0.,1.);}',
    // The sweep is clipped by the glyph alpha; the surrounding background stays dark.
    fragment:`precision mediump float;
      varying vec2 uv;
      uniform sampler2D lettering;
      uniform float visibility,sweepTime,sweepEnabled;
      void main(){
        vec4 ink=texture2D(lettering,uv);
        float centre=mix(-.2,1.2,sweepTime/24.);
        float distance=(uv.x+.2*(uv.y-.5)-centre)/.065;
        float light=exp(-distance*distance)*sweepEnabled;
        vec3 gold=mix(ink.rgb,vec3(.82,.74,.55),light*.12);
        gl_FragColor=vec4(gold,ink.a*visibility*(1.+.58*light));
      }`
  };
})();
