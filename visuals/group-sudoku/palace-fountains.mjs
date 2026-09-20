import * as T from '../3d/vendor/three.module.js';
// Shared musical envelope drives the whole court; no extra audio playback or microphone.
export function fountainHeight(kind,energy,bass){return kind==='crown'?.65+energy*1.8+bass*.8:.25+energy*.90+bass*.22;}
export function installPalaceFountains(a,p){
 const rim=new T.MeshStandardMaterial({color:0xcbd7cd,roughness:.55}),water=new T.MeshStandardMaterial({color:0x599caa,metalness:.26,roughness:.20}),bronze=new T.MeshStandardMaterial({color:0xac9056,metalness:.6,roughness:.35});
 const root=new T.Group();root.userData.landmark='musical-palace-water-court';p.add(root);a.palaceFountains={root,jets:[],ripples:[]};
 // One connected U-shaped channel and a foreground crown basin.
 for(const side of [-1,1]){a.box(root,[.78,.16,11.8],[side*6.55,.30,0],rim);a.box(root,[.57,.025,11.6],[side*6.55,.40,0],water);}
 a.box(root,[13.8,.16,.9],[0,.30,6.25],rim);a.box(root,[13.55,.025,.66],[0,.40,6.25],water);
 a.box(root,[.70,.16,2.2],[0,.30,7.1],rim);a.box(root,[.48,.026,2.15],[0,.40,7.1],water);
 a.cylinder(root,1.36,.18,[0,.31,8.05],rim);a.cylinder(root,1.20,.025,[0,.416,8.05],water);a.torus(root,1.28,.065,[0,.46,8.05],rim);
 function jet(x,z,dx,dz,kind,phase){const geo=new T.BufferGeometry();geo.setAttribute('position',new T.BufferAttribute(new Float32Array(33*3),3));const m=new T.LineBasicMaterial({color:0xc7eff1,transparent:true,opacity:.7,depthWrite:false});const line=new T.Line(geo,m);line.frustumCulled=false;root.add(line);const particles=new T.Points(new T.BufferGeometry().setAttribute('position',new T.BufferAttribute(new Float32Array(12*3),3)),new T.PointsMaterial({color:0xe7ffff,size:.062,transparent:true,opacity:.8,depthWrite:false}));particles.frustumCulled=false;root.add(particles);a.cylinder(root,.075,.065,[x,.46,z],bronze);a.palaceFountains.jets.push({line,particles,x,z,dx,dz,kind,phase});}
 for(const side of [-1,1])for(let j=0;j<5;j++)jet(side*6.55,-4.4+j*2.2,0,.37,'arc',j*.6+(side+1));
 for(let j=-4;j<=4;j++)jet(j*1.30,6.25,.30,0,'arc',j*.45);
 for(let j=0;j<7;j++){const q=j*Math.PI*2/7;jet(Math.sin(q)*.30,8.05+Math.cos(q)*.30,Math.sin(q)*.52,Math.cos(q)*.52,'crown',j*.3);}
 for(let j=0;j<3;j++){const points=Array.from({length:64},(_,k)=>new T.Vector3(Math.sin(k*Math.PI/32),0,Math.cos(k*Math.PI/32)));const line=new T.LineLoop(new T.BufferGeometry().setFromPoints(points),new T.LineBasicMaterial({color:0xc8f1f0,transparent:true,opacity:.4,depthWrite:false}));line.position.set(0,.44,8.05);root.add(line);a.palaceFountains.ripples.push({line,phase:j/3});}
 updatePalaceFountains(a.palaceFountains,0,{energy:0,bass:0},false,false);
}
export function updatePalaceFountains(f,time,levels,reduced,ready){if(!f)return;const energy=reduced?0:(levels?.energy||0),bass=reduced?0:(levels?.bass||0),t=reduced?0:time;for(const jet of f.jets){const h=fountainHeight(jet.kind,energy,bass)*(reduced?1:.95+.05*Math.sin(t*1.3+jet.phase)),position=jet.line.geometry.attributes.position;function point(u){return [jet.x+jet.dx*u,.47+4*h*u*(1-u),jet.z+jet.dz*u];}for(let j=0;j<33;j++)position.setXYZ(j,...point(j/32));position.needsUpdate=true;jet.line.visible=ready;jet.line.material.opacity=.50+energy*.38;jet.line.material.color.setRGB(.55+energy*.25,.83+energy*.15,.90+energy*.10);const pp=jet.particles.geometry.attributes.position;for(let j=0;j<12;j++)pp.setXYZ(j,...point((t*.55+j/12+jet.phase)%1));pp.needsUpdate=true;jet.particles.visible=ready&&!reduced;}for(const r of f.ripples){const u=(t*.34+r.phase)%1;r.line.scale.setScalar(.25+u*.88);r.line.material.opacity=(1-u)*(.25+energy*.35);r.line.visible=ready;}}
