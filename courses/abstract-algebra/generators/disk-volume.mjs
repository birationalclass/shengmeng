// Shared density for disk emission and three-dimensional extinction.
export const diskDensityGLSL=` float hash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7))+seed)*43758.5453);}float noise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(hash(i),hash(i+vec2(1,0)),f.x),mix(hash(i+vec2(0,1)),hash(i+vec2(1,1)),f.x),f.y);}float fbm(vec2 p){return .57*noise(p)+.28*noise(p*2.07+7.)+.15*noise(p*4.13+17.);}
 float diskDensity(vec2 q){float r=length(q);if(r<inner||r>1.)return 0.;float a=atan(-q.y,q.x),cloud=fbm(q*13.),fine=fbm(q*48.),phase=profile.x*(a-profile.y*log(r+.12));float arms=pow(.5+.5*cos(phase+(cloud-.5)*2.7),3.);float taper=smoothstep(inner,inner+.035,r)*(1.-smoothstep(.7,1.,r));float lane=smoothstep(.24,.64,fbm(q*24.+vec2(cos(phase),sin(phase))*.35));float clumps=smoothstep(.3,.8,cloud);float density=(.12+arms*.88)*(.3+clumps*1.8)*(.18+.82*lane)*taper;density*=.7+.3*sin(a+seed);
return density;}`;
export function bindDiskExtinction(T,root,cloud,outer){
 const inverse={value:new T.Matrix4()},eye={value:new T.Vector3()};
 const uniforms={diskInverse:inverse,diskEye:eye,diskCameraWorld:{value:new T.Matrix4()},inner:cloud.material.uniforms.inner,profile:cloud.material.uniforms.profile,diskOpacity:cloud.material.uniforms.opacity};
 const fragment=`varying vec3 volumePosition;uniform vec3 diskEye;uniform float inner;uniform vec4 profile;uniform float seed;uniform float diskOpacity;
 ${diskDensityGLSL.replaceAll('hash(', 'volumeHash(').replaceAll('noise(', 'volumeNoise(').replaceAll('fbm(', 'volumeFbm(').replaceAll('seed','volumeSeed')}
 float diskTransmission(vec3 point){
  vec3 delta=diskEye-point;float distanceToEye=length(delta);vec3 ray=delta/max(distanceToEye,.00001);
  if(abs(ray.y)<.00001)return 1.;
  float a=(-.04-point.y)/ray.y,b=(.04-point.y)/ray.y;
  float begin=max(0.,min(a,b)),end=min(distanceToEye,max(a,b));if(end<=begin)return 1.;
  float stepLength=(end-begin)/16.,tau=0.;
  for(int i=0;i<16;i++){vec3 samplePoint=point+ray*(begin+(float(i)+.5)*stepLength);float r=length(samplePoint.xz);float u=clamp((r-inner)/(1.-inner),0.,1.);float height=.003+.012*sin(3.14159265*u);
   tau+=diskDensity(vec2(samplePoint.x,-samplePoint.z))*exp(-.5*pow(samplePoint.y/height,2.))*stepLength/.018;
  }
  return exp(-tau*(.65+diskOpacity)*.9);
 }`;
 // A separate seed avoids collisions with the procedural body textures.
 const shaderFragment=fragment.replace('uniform float seed;', 'uniform float volumeSeed;');
 root.userData.planets.filter(body=>body.userData.order!==1).forEach(body=>body.traverse(part=>{
  const m=part.material;if(!m?.isShaderMaterial)return;
  Object.assign(m.uniforms,uniforms);m.uniforms.volumeSeed=cloud.material.uniforms.seed;
  // Billboard coronas must use their expanded view-space vertex, not the unrotated quad.
  const point=m.vertexShader.includes('mv.xy+=')?'diskCameraWorld*mv':'modelMatrix*vec4(position,1.)';
  m.vertexShader='varying vec3 volumePosition;uniform mat4 diskInverse;uniform mat4 diskCameraWorld;\n'+m.vertexShader.replace(/}\s*$/,`volumePosition=(diskInverse*(${point})).xyz;}`);
  m.fragmentShader=shaderFragment+'\n'+m.fragmentShader.replace(/}\s*$/, 'gl_FragColor.rgb*=diskTransmission(volumePosition);}');
  m.needsUpdate=true;
 }));
 return camera=>{cloud.updateWorldMatrix(true,false);inverse.value.copy(cloud.matrixWorld).invert().premultiply(new T.Matrix4().makeScale(1/outer,1/outer,1/outer));eye.value.copy(camera.position).applyMatrix4(inverse.value);uniforms.diskCameraWorld.value.copy(camera.matrixWorld);};
}


