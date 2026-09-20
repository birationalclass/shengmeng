import * as T from '../3d/vendor/three.module.js';
// A fixed GPU buffer: three staggered rockets, each opening into a sevenfold bloom.
export function installFireworks(a,parent){
 const count=3*112*5,position=new Float32Array(count*3),seeds=new Float32Array(count*3);let i=0;
 for(let rocket=0;rocket<3;rocket++)for(let ray=0;ray<112;ray++)for(let tail=0;tail<5;tail++){
  seeds.set([rocket,ray,tail],i*3);i++;
 }
 const geometry=new T.BufferGeometry();geometry.setAttribute('position',new T.BufferAttribute(position,3));geometry.setAttribute('seed',new T.BufferAttribute(seeds,3));
 const material=new T.ShaderMaterial({transparent:true,depthWrite:false,blending:T.AdditiveBlending,uniforms:{uTime:{value:0}},vertexShader:`
 attribute vec3 seed;uniform float uTime;varying vec3 vColor;varying float vAlpha;
 void main(){
 float rocket=seed.x,ray=seed.y,tail=seed.z;
 float age=mod(uTime+rocket*2.1,6.3)-tail*.036;
 vec3 origin=vec3(rocket<.5?-9.6:(rocket<1.5?9.6:0.0),1.4,rocket<1.5?-5.8:-12.0);
 vec3 p=origin;vAlpha=0.0;
 vColor=rocket<.5?vec3(1.0,.66,.24):(rocket<1.5?vec3(.4,.78,1.0):vec3(1.0,.48,.73));
 if(age>=0.0&&age<1.15){
 p.y+=age*6.7;p.x+=sin(age*2.0+rocket)*.3;
 vAlpha=ray<1.0?(1.0-tail*.17):0.0;
 }else if(age>=1.15&&age<4.6){
 float t=age-1.15,angle=ray*2.39996323;
 float vertical=1.0-2.0*(ray+.5)/112.0;
 float r=sqrt(max(0.0,1.0-vertical*vertical));
 vec3 dir=vec3(r*cos(angle),vertical,r*sin(angle));
 float speed=2.0+.65*cos(angle*7.0);
 p+=vec3(0.0,7.7,0.0)+dir*speed*(1.0-exp(-t*.8))/ .8;
 p.y-=.48*t*t;
 vAlpha=pow(max(0.0,1.0-t/3.45),1.3)*(1.0-tail*.17)*(.82+.18*sin(t*19.0+ray*4.0));
 }
 vec4 mv=modelViewMatrix*vec4(p,1.0);gl_Position=projectionMatrix*mv;
 gl_PointSize=clamp((tail<.5?240.0:150.0)/max(1.0,-mv.z),2.0,8.0);
 }
 `,fragmentShader:`varying vec3 vColor;varying float vAlpha;void main(){float d=length(gl_PointCoord-.5)*2.0;if(d>1.0||vAlpha<.01)discard;gl_FragColor=vec4(vColor*2.2,vAlpha*pow(1.0-d,1.1));
 #include <tonemapping_fragment>
 #include <colorspace_fragment>
 }`});
 const points=new T.Points(geometry,material);points.name='seven-star-fireworks';points.frustumCulled=false;points.visible=false;parent.add(points);a.fireworks=points;
}
export function updateFireworks(points,time,reduced,ready){if(!points)return;points.visible=ready&&!reduced;if(points.visible)points.material.uniforms.uTime.value=time;}
