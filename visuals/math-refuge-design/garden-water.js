import * as THREE from 'three';
import {riverPoint,BUILDING_SCALE} from './site-layout.js?v44-hall-clearance';

// One connected geometric watercourse; no extra planar reflection rendering.
export function createGardenWater(scene){
  const position=[],uv=[],indices=[],speed=[],foam=[],count=312,across=8;
  let distance=0,previous;
  for(let i=0;i<=count;i++){
    const t=i/count,p=riverPoint(t),a=riverPoint(Math.max(0,t-.001)),b=riverPoint(Math.min(1,t+.001));
    const length=Math.hypot(b.x-a.x,b.z-a.z),nx=-(b.z-a.z)/length,nz=(b.x-a.x)/length;
    const fall=Math.max(0,Math.min(1,(a.y-b.y)/length/2));
    if(previous)distance+=Math.hypot(p.x-previous.x,p.y-previous.y,p.z-previous.z);previous=p;
    for(let j=0;j<=across;j++){
      const u=j/across,w=(u*2-1)*p.width;
      position.push(p.x+nx*w,p.y+.035*Math.sin(i*.6+j)*fall,p.z+nz*w);uv.push(u,distance/3);speed.push(fall);
      foam.push(Math.exp(-Math.pow((t-2/8)*55,2)));
      if(i<count&&j<across){const k=i*(across+1)+j;indices.push(k,k+1,k+across+1,k+1,k+across+2,k+across+1);}
    }
  }
  const geometry=new THREE.BufferGeometry();geometry.setAttribute('position',new THREE.Float32BufferAttribute(position,3));geometry.setAttribute('uv',new THREE.Float32BufferAttribute(uv,2));geometry.setAttribute('fallSpeed',new THREE.Float32BufferAttribute(speed,1));geometry.setAttribute('splash',new THREE.Float32BufferAttribute(foam,1));geometry.setIndex(indices);geometry.computeVertexNormals();
  const clock={value:0};
  const material=new THREE.ShaderMaterial({side:THREE.DoubleSide,fog:true,uniforms:THREE.UniformsUtils.merge([THREE.UniformsLib.fog,{time:clock}]),vertexShader:`
    attribute float fallSpeed;attribute float splash;varying vec2 vUV;varying float vFall;varying float vSplash;
    #include <fog_pars_vertex>
    void main(){vUV=uv;vFall=fallSpeed;vSplash=splash;vec4 mvPosition=modelViewMatrix*vec4(position,1.0);gl_Position=projectionMatrix*mvPosition;
    #include <fog_vertex>
    }`,fragmentShader:`
    uniform float time;varying vec2 vUV;varying float vFall;varying float vSplash;
    #include <common>
    #include <fog_pars_fragment>
    void main(){
      float flow=vUV.y-time*(.35+vFall*1.7);
      float thread=pow(.5+.5*sin(vUV.x*149.0+sin(flow*6.0)*.8),7.0);
      float wave=.5+.5*sin(flow*16.0+sin(vUV.x*24.0)*1.2);
      float edge=smoothstep(.72,1.0,abs(vUV.x*2.0-1.0));
      float white=clamp(vFall*(.22+thread*.75)+vSplash*wave*.85+edge*wave*.3,0.0,1.0);
      vec3 color=mix(vec3(.035,.16,.14),vec3(.12,.36,.30),wave*.4);
      color=mix(color,vec3(.80,.88,.82),white);
      gl_FragColor=vec4(color,1.0);
      #include <tonemapping_fragment>
      #include <colorspace_fragment>
      #include <fog_fragment>
    }`});
  const mesh=new THREE.Mesh(geometry,material);mesh.name='Connected waterfall and winding creek';mesh.scale.setScalar(BUILDING_SCALE);scene.add(mesh);
  // A small, bounded splash spray at the plunge pool, not a full-screen fog pass.
  const sprayGeometry=new THREE.BufferGeometry(),spray=[];
  const plunge=riverPoint(2/8);
  for(let i=0;i<80;i++){const a=i*2.399,r=.4+(i%13)/13*2.5;spray.push(plunge.x+Math.cos(a)*r,plunge.y+.1+(i%7)*.18,plunge.z+Math.sin(a)*r);}
  sprayGeometry.setAttribute('position',new THREE.Float32BufferAttribute(spray,3));
  const sprayMaterial=new THREE.PointsMaterial({color:'#d7ece3',size:.09,transparent:true,opacity:.36,depthWrite:false,sizeAttenuation:true});
  const mist=new THREE.Points(sprayGeometry,sprayMaterial);mist.name='Waterfall splash droplets';mist.scale.setScalar(BUILDING_SCALE);scene.add(mist);
  const bridgeGeometry=new THREE.BoxGeometry(1.9,1.65,.78),bridgeMaterial=new THREE.MeshStandardMaterial({color:'#9b9d89',roughness:.9});
  const bridge=new THREE.InstancedMesh(bridgeGeometry,bridgeMaterial,7),matrix=new THREE.Matrix4();bridge.name='Creek crossing stepping stones';
  const crossing=riverPoint(.71);
  for(let i=0;i<7;i++){matrix.makeTranslation(crossing.x,crossing.y-.45,crossing.z-2.7+i*.9);bridge.setMatrixAt(i,matrix);}bridge.scale.setScalar(BUILDING_SCALE);bridge.receiveShadow=true;scene.add(bridge);
  return {mesh,update(dt){material.uniforms.time.value+=dt;const t=material.uniforms.time.value;mist.position.y=Math.sin(t*.8)*.12;sprayMaterial.opacity=.29+Math.sin(t*.6)*.05;},dispose(){geometry.dispose();material.dispose();sprayGeometry.dispose();sprayMaterial.dispose();bridgeGeometry.dispose();bridgeMaterial.dispose();}};
}
