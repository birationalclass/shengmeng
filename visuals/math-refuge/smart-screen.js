// Same calligraphic Chinese / old-style serif Latin families as the spectral cover.
export const SCREEN_FONT='RefugeChinese, Baskerville, "Iowan Old Style", "Palatino Linotype", Georgia, serif';
export function silverInk(ctx,height=240){
  if(!ctx.createLinearGradient)return '#d9e5e4';
  const gradient=ctx.createLinearGradient(0,0,0,height);
  for(const [stop,color] of [[0,'#fbf8ed'],[.37,'#dce2df'],[.54,'#a8b8b9'],[.76,'#e2e8e1'],[1,'#b3c2c0']])gradient.addColorStop(stop,color);
  return gradient;
}
export function seminarDate(now=new Date()){
  return new Intl.DateTimeFormat('en-CA',{timeZone:'Asia/Shanghai',year:'numeric',month:'2-digit',day:'2-digit'}).format(now).replaceAll('-','.');
}
export function addTextSheen(T,mesh,texture,width,height){
  const material=new T.ShaderMaterial({transparent:true,depthWrite:false,toneMapped:false,uniforms:{labelMap:{value:texture},progress:{value:0},strength:{value:0}},
    vertexShader:'varying vec2 uvLabel; void main(){uvLabel=uv;gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.0);}',
    fragmentShader:'uniform sampler2D labelMap; uniform float progress; uniform float strength; varying vec2 uvLabel; void main(){float ink=texture2D(labelMap,uvLabel).a;float band=1.0-smoothstep(0.025,0.16,abs(uvLabel.x-uvLabel.y*0.12-(progress*1.5-0.25)));gl_FragColor=vec4(0.93,1.0,0.98,ink*band*strength);}'
  });
  const sweep=new T.Mesh(new T.PlaneGeometry(width,height),material);sweep.position.z=.012;sweep.name='Text-only hover sheen';mesh.add(sweep);
  mesh.userData.sheen={material,elapsed:2,wasHovered:false};return sweep;
}
export function updateGlassFeedback(mesh,dt,reduced=false){
  if(!mesh.userData.smartGlass)return;
  const data=mesh.userData,hovered=Boolean(data.hovered&&data.action),pressed=Boolean(data.pressed&&data.action);
  const state=data.feedback||(data.feedback={scale:1,pulse:0,base:[mesh.scale.x,mesh.scale.y,mesh.scale.z]});
  state.pulse=Math.max(state.pulse,Number(data.clickPulse)||0);data.clickPulse=0;
  state.pulse=Math.max(0,state.pulse-Math.max(0,dt)*2.8);
  const target=pressed?.94:1+(hovered?.025:0)+state.pulse*.035;
  state.scale=reduced?1:state.scale+(target-state.scale)*(1-Math.exp(-Math.max(0,dt)*22));
  mesh.scale.set(state.base[0]*state.scale,state.base[1]*state.scale,state.base[2]);mesh.updateMatrix();
  const label=mesh.children.find(o=>o.userData.screenLabel)||mesh,color=label.material?.color;
  if(color){const warmth=pressed?1:state.pulse,k=1-Math.exp(-Math.max(0,dt)*16),base=hovered?1:.9;
    color.r+=(1-color.r)*k;color.g+=(base+(1-base)*warmth-color.g)*k;color.b+=(base-(base-.72)*warmth-color.b)*k;
  }
}
export function updateTextSheen(T,mesh,dt,reduced){
  updateGlassFeedback(mesh,dt,reduced);
  const state=mesh.userData.sheen;if(!state)return;
  const hovered=Boolean(mesh.userData.hovered&&mesh.userData.action);
  if(hovered&&!state.wasHovered)state.elapsed=0;state.wasHovered=hovered;state.elapsed+=dt;
  state.material.uniforms.progress.value=Math.min(1,state.elapsed/.85);
  state.material.uniforms.strength.value=hovered&&!reduced&&state.elapsed<.85?.8:0;
}
