import * as T from 'three';
// A compact sky-view LUT: spherical atmosphere, single scattering and Beer-Lambert
// extinction. Inspired by Bruneton / Hillaire; not their full multiple-scattering solver.
// Distances are kilometres. Rayleigh scale height 8 km; aerosol scale height 1.2 km.
export function createAtmosphereLUT(renderer,device={}){
 if(!renderer?.isWebGLRenderer||device.safe||!renderer.extensions.has('EXT_color_buffer_float'))return null;
 const size=device.atmosphereSize||256,interval=device.atmosphereInterval||250;
 const target=new T.WebGLRenderTarget(size,size/2,{type:T.HalfFloatType,depthBuffer:false,stencilBuffer:false});
 target.texture.wrapS=T.RepeatWrapping;
 const uniforms={sun:{value:new T.Vector3(1,1,0).normalize()},aerosol:{value:1}};
 const material=new T.ShaderMaterial({uniforms,depthTest:false,depthWrite:false,vertexShader:'varying vec2 uvSky;void main(){uvSky=uv;gl_Position=vec4(position.xy,0.,1.);}',fragmentShader:`
 precision highp float;varying vec2 uvSky;uniform vec3 sun;uniform float aerosol;
 const float R=6360.,TOP=6460.,PI=3.14159265359;
 const vec3 betaR=vec3(.005802,.013558,.033100),ozone=vec3(.000650,.001881,.000085);
 float exitDistance(vec3 p,vec3 d,float r){float b=dot(p,d);return -b+sqrt(max(0.,b*b-dot(p,p)+r*r));}
 vec3 density(vec3 p){float h=max(0.,length(p)-R);return vec3(exp(-h/8.),exp(-h/1.2),max(0.,1.-abs(h-25.)/15.));}
 vec3 extinction(vec3 od){return betaR*od.x+vec3(.00444*aerosol)*od.y+ozone*od.z;}
 vec3 solarTransmission(vec3 p){float b=dot(p,sun),disc=b*b-dot(p,p)+R*R;if(b<0.&&disc>0.)return vec3(0.);float length=exitDistance(p,sun,TOP);vec3 od=vec3(0.);for(int j=0;j<8;j++){float a=float(j)/8.,b=float(j+1)/8.;float t0=length*a*a,t1=length*b*b;od+=density(p+sun*((t0+t1)*.5))*(t1-t0);}return exp(-extinction(od));}
 void main(){float az=(uvSky.x-.5)*2.*PI;float elevation=uvSky.y*uvSky.y*PI*.5;vec3 d=vec3(cos(az)*cos(elevation),sin(elevation),sin(az)*cos(elevation));vec3 origin=vec3(0.,R+.015,0.);float distance=exitDistance(origin,d,TOP);vec3 optical=vec3(0.),radiance=vec3(0.);float mu=dot(d,sun),phaseR=3./(16.*PI)*(1.+mu*mu),g=.8;float phaseM=3./(8.*PI)*(1.-g*g)*(1.+mu*mu)/((2.+g*g)*pow(max(.001,1.+g*g-2.*g*mu),1.5));
 for(int i=0;i<24;i++){float a=float(i)/24.,b=float(i+1)/24.;float t0=distance*a*a,t1=distance*b*b,stepLength=t1-t0;vec3 p=origin+d*((t0+t1)*.5),rho=density(p),segment=rho*stepLength;vec3 transmit=exp(-extinction(optical+segment*.5))*solarTransmission(p);radiance+=transmit*(betaR*rho.x*phaseR+vec3(.003996*aerosol)*rho.y*phaseM)*stepLength;optical+=segment;}
 gl_FragColor=vec4(radiance*8.,1.);}`});
 const scene=new T.Scene(),quad=new T.Mesh(new T.PlaneGeometry(2,2),material),camera=new T.Camera();scene.add(quad);
 let key='',last=-Infinity;
 return {texture:target.texture,update(sun,cloud){const next=[sun.x,sun.y,sun.z,cloud].map(v=>v.toFixed(3)).join(','),now=performance.now();if(next===key||now-last<interval)return;key=next;last=now;uniforms.sun.value.copy(sun).normalize();uniforms.aerosol.value= .12+cloud*2.;const previous=renderer.getRenderTarget(),auto=renderer.autoClear;try{renderer.autoClear=true;renderer.setRenderTarget(target);renderer.render(scene,camera);}finally{renderer.setRenderTarget(previous);renderer.autoClear=auto;}},dispose(){target.dispose();quad.geometry.dispose();material.dispose();}};
}
