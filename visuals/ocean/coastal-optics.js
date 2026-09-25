// Experimental optical model; shared by exposed sand and refracted seabed.
export const coastalOptics = `
vec2 coastCoordinates(vec2 p){return vec2(dot(p,vec2(.94,.341174)),dot(p,vec2(.341174,-.94)));}
vec3 sandAlbedo(vec2 ca){
 float ripple=sin(ca.x*8.+noise(ca*.65)*3.+sin(ca.y*.8))*.5+.5;
 float filtered=1.-smoothstep(.3,1.5,length(fwidth(ca*8.)));
 float grains=noise(ca*95.);
 float gf=1.-smoothstep(.3,1.,length(fwidth(ca*95.)));
 return vec3(.48,.365,.235)*(.90+.10*noise(ca*1.8)+.045*ripple*filtered+.06*(grains-.5)*gf);
}
vec3 coastIrradiance(vec3 n){
 float day=smoothstep(5.,22.,uSun), dusk=1.-smoothstep(-3.,3.,uSun);
 vec3 ambient=mix(vec3(.22,.28,.38),vec3(.48,.64,.78),day);
 vec3 sunlight=mix(vec3(1.8,.88,.34),vec3(1.6,1.52,1.35),day);
 return ambient*(.65+.35*max(0.,n.y))*(1.-dusk*.55)
       +sunlight*max(0.,dot(n,sunDirection()))*smoothstep(-4.,3.,uSun);
}
vec3 transmittedWater(vec3 p,vec3 view,vec3 n){
 vec3 ray=refract(-view,n,1./1.333);
 // Refine intersection with the actual sloping seabed. Far paths are opaque.
 float travel=clamp((p.y-beachHeight(coastCoordinates(p.xz)))/max(.08,-ray.y),0.,60.);
 for(int i=0;i<3;i++){
  vec3 hit=p+ray*travel;vec2 ca=coastCoordinates(hit.xz);
  float residual=hit.y-beachHeight(ca);
  float slope=.055*dot(ray.xz,vec2(.94,.341174));
  travel=clamp(travel+residual/max(.08,-ray.y+slope),0.,60.);
 }
 vec2 bottom=coastCoordinates((p+ray*travel).xz);
 vec3 extinction=vec3(.43,.105,.070);
 vec3 transmission=exp(-extinction*travel);
 float bottomDepth=max(0.,p.y-beachHeight(bottom));
 vec3 bottomLight=exp(-extinction*bottomDepth/max(.28,sunDirection().y));
 vec3 sand=sandAlbedo(bottom)*.57*coastIrradiance(normalize(vec3(-.052,1.,-.019)))*bottomLight;
 float day=smoothstep(5.,22.,uSun);
 vec3 scatter=mix(vec3(.014,.092,.105),vec3(.025,.24,.255),day);
 scatter*=.7+.3*max(0.,n.y);
 return sand*transmission+scatter*(1.-transmission);
}
`;

export const capillaryNormals = `
 #ifdef COASTAL_OPTICS
 slope=vec2(0.);
 for(int i=0;i<9;i++){
  float band=float(i),k=9.*pow(1.55,band);
  vec2 dir=vec2(cos(band*2.399+.3),sin(band*2.399+.3));
  float packet=noise(uv*.42+band*7.1);
  float phase=dot(uv,dir)*k+packet*4.-uTime*sqrt(9.81*k+.000074*k*k*k)+band*17.31;
  float visible=1.-smoothstep(.65,2.8,fwidth(phase));
  slope+=dir*cos(phase)*visible*pow(.76,band)*(.35+.55*packet);
 }
 detail=(.035+.065*uWind)*smoothstep(.005,.18,waterThickness)*(1.-vProfile.b*.65);
 #endif
`;

export const opticalBody = `
 #ifdef COASTAL_OPTICS
 body=transmittedWater(vWorld,view,n);
 // Direct sun belongs to the microfacet term, not also the reflected disk.
 reflected-=vec3(5.,3.75,1.85)*(1.-smoothstep(.009,.012,length(r-sd)))*(1.-dusk*.7);
 reflected=max(reflected,vec3(0.));
 #endif
`;

export const opticalReflection = `
 #ifdef COASTAL_OPTICS
 float nv=max(.03,dot(n,view)),nl=max(0.,dot(n,sd));
 float variance=dot(dFdx(n),dFdx(n))+dot(dFdy(n),dFdy(n));
 float alpha2=max(.00016,pow(.10+uWind*.06,4.)+variance*.22);
 float denom=nh*nh*(alpha2-1.)+1.;
 float distribution=alpha2/(PI*denom*denom);
 float gv=2.*nv/(nv+sqrt(alpha2+(1.-alpha2)*nv*nv));
 float gl=2.*nl/max(.001,nl+sqrt(alpha2+(1.-alpha2)*nl*nl));
 col=body*(1.-fresnel)+reflection*fresnel;
 col+=light*min(18.,distribution*sf*gv*gl/(4.*nv))*smoothstep(-4.,1.,uSun);
 #endif
`;

export const opticalBeach = `
 #ifdef COASTAL_OPTICS
 col=sandAlbedo(vCA)*mix(1.,.57,wet)*coastIrradiance(n);
 float f=.0204+.9796*pow(1.-sat(dot(n,view)),5.);
 col=mix(col,sky(r,true),wet*f*.8);
 #endif
`;
