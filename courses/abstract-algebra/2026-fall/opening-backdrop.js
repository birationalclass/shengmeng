/* Dark mathematical logos stay beneath the sand; captions are foreground DOM. */
(() => {
  'use strict';
  const scenes = [
    {logo:'D₆',title:'六瓣玫瑰',zh:'旋转六十度，花瓣重新重合。旋转与反射组成二面体群 D₆。',en:'Six petals. Rotations and reflections form the dihedral group D₆.'},
    {logo:'D₈',title:'八角星',zh:'八次旋转，八面镜像。十六个对称变换，在复合运算下组成群。',en:'Eight rotations and eight reflections: sixteen symmetries, one group.'},
    {logo:'D₁₂',title:'十二重花窗',zh:'每转三十度，花窗便与自身重合。对称把局部的重复连成整体。',en:'A thirty-degree turn brings the window back to itself.'},
    {logo:'E₈',title:'Lie Group',kind:'explanation',zh:'E₈ 根系\n八维空间中的 240 个根投向平面；交织的线条留下高维对称的影子。',en:'E₈ Root System\n240 roots in eight dimensions, projected onto a plane.'},
    {logo:'ℂ',title:'Julia 分形',zh:'在复平面反复施行同一个映射。迭代的边界，蕴藏无尽的细节。',en:'Iteration in the complex plane reveals an endlessly intricate boundary.'},
    {logo:'ℤ',title:'THE LORD OF THE RING',zh:'整数环是含幺环的起点：到每个含幺环，都有唯一的保幺环同态。',en:'From ℤ to every unital ring, there is a unique unital homomorphism.',kind:'ring-verse',verse:{en:'One Ring to rule them all,\nOne Ring to find them,\nOne Ring to bring them all,\nand in the darkness bind them.',zh:'一戒统御众戒，\n一戒寻觅众戒，\n一戒召集众戒，\n于黑暗中将众戒尽缚。'}},
    {logo:'Δ',title:'Platonic Solids',kind:'theorem',en:'Triangle Groups\nUp to similarity, there are exactly five convex regular polyhedra in three-dimensional Euclidean space: tetrahedron, cube, octahedron, dodecahedron, and icosahedron.\n\nRotation groups\nΔ⁺(2,3,3) ≅ A₄: tetrahedron\nΔ⁺(2,3,4) ≅ S₄: cube, octahedron\nΔ⁺(2,3,5) ≅ A₅: dodecahedron, icosahedron',zh:'三角群\n定理　在三维欧氏空间中，凸正多面体按相似分类恰有五种：正四面体、正六面体、正八面体、正十二面体、正二十面体。\n\n保向球面三角群\nΔ⁺(2,3,3) ≅ A₄：四面体\nΔ⁺(2,3,4) ≅ S₄：六、八面体\nΔ⁺(2,3,5) ≅ A₅：十二、二十面体'},
    {logo:'π₁',title:'Fundamental Group',kind:'explanation',en:'The same fundamental group\nThe Möbius band M deformation retracts onto its core circle S¹. Their fundamental groups are therefore isomorphic.\n\nπ₁(M) ≅ π₁(S¹) ≅ ℤ',zh:'相同的基本群\nMöbius 带 M 可形变收缩到其中心圆 S¹，因而二者的基本群同构。\n\nπ₁(M) ≅ π₁(S¹) ≅ ℤ'},
    {logo:'17',title:'Gauss · 17-Gon',kind:'explanation',en:'Gauss, 1796\n17 = 2⁴ + 1 is a Fermat prime.\nThe regular 17-gon is constructible with compass and straightedge.',zh:'高斯，1796 年\n17 = 2⁴ + 1 是费马素数。\n正十七边形可用尺规作图。'},
    {logo:'Gal(f)',title:'Galois Group',kind:'explanation',en:'Évariste Galois · 1811–1832\nA French mathematician who linked the symmetries of polynomial roots to solvability by radicals, laying foundations for group theory.\nHe died after a duel, aged twenty.',zh:'埃瓦里斯特·伽罗瓦 · 1811–1832\n法国数学家，将方程根的对称性与根式可解性联系起来，奠定群论的重要基础。\n因决斗负伤去世，年仅二十岁。'}
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
        const size=Math.min(height*.74,width*.57)*(index===9?.46:1);
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
