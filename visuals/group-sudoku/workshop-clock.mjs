import * as T from '../3d/vendor/three.module.js';
export function clockAngles(date){const seconds=date.getSeconds()+date.getMilliseconds()/1000,minutes=date.getMinutes()+seconds/60,hours=date.getHours()%12+minutes/60;return {hour:-hours*Math.PI/6,minute:-minutes*Math.PI/30,second:-seconds*Math.PI/30};}
export function installWorkshopClock(a,parent){
 const root=new T.Group();root.position.set(0,6.65,-8.6);root.userData.landmark='grand-astronomical-clock';parent.add(root);
 const brass=new T.MeshStandardMaterial({color:0xc6a05d,metalness:.7,roughness:.32}),steel=new T.MeshStandardMaterial({color:0x33444b,metalness:.65,roughness:.4}),ivory=new T.MeshStandardMaterial({color:0xe3dcc4,roughness:.72}),ink=new T.MeshStandardMaterial({color:0x253338,metalness:.35,roughness:.42}),red=new T.MeshStandardMaterial({color:0xa54f39,metalness:.3});
 for(const x of [-1.85,1.85]){a.box(root,[.19,3.5,.3],[x,-2.7,-.25],steel);a.rod(root,[x,-4.25,-.25],[x*.40,-2.3,-.25],.055,brass);}
 const body=a.cylinder(root,2.38,.28,[0,0,0],steel);body.rotation.x=Math.PI/2;const face=a.cylinder(root,2.20,.05,[0,0,.18],ivory);face.rotation.x=Math.PI/2;
 for(const [r,t,z]of [[2.36,.08,.14],[2.24,.055,.23],[1.72,.018,.25]])a.mesh(root,new T.TorusGeometry(r,t,8,80),brass,[0,0,z]);
 for(let j=0;j<60;j++){const q=j*Math.PI/30,r=j%5===0?2.03:2.09;const tick=a.box(root,[j%5===0?.055:.020,j%5===0?.23:.10,.025],[Math.sin(q)*r,Math.cos(q)*r,.24],j%5===0?ink:brass);tick.rotation.z=-q;}
 if(typeof document!=='undefined'){const c=document.createElement('canvas');c.width=c.height=1024;const x=c.getContext('2d');x.clearRect(0,0,1024,1024);x.fillStyle='#34413e';x.textAlign='center';x.textBaseline='middle';x.font='52px Georgia';const numerals=['XII','I','II','III','IV','V','VI','VII','VIII','IX','X','XI'];for(let j=0;j<12;j++){const q=j*Math.PI/6;x.fillText(numerals[j],512+Math.sin(q)*398,512-Math.cos(q)*398);}x.font='18px Georgia';x.fillStyle='#8b754b';x.fillText('TEMPUS · LOCAL TIME',512,310);const tex=new T.CanvasTexture(c);tex.colorSpace=T.SRGBColorSpace;a.mesh(root,new T.PlaneGeometry(4.4,4.4),new T.MeshBasicMaterial({map:tex,transparent:true,depthWrite:false}),[0,0,.255]);}
 // Three small dial apertures expose linked wheels; the lower spindle joins the gear wall.
 for(const [i,x]of [-.73,0,.73].entries()){const frame=a.cylinder(root,.39,.06,[x,-.79,.27],steel);frame.rotation.x=Math.PI/2;const carrier=new T.Group();carrier.position.set(x,-.79,.32);carrier.rotation.x=Math.PI/2;root.add(carrier);a.gear(carrier,.37,12,[0,0,0],(i%2?-1:1)*Math.PI/30,brass);a.mesh(root,new T.TorusGeometry(.39,.025,6,24),brass,[x,-.79,.33]);}
 a.rod(root,[0,-3.05,-.06],[0,-1.20,-.06],.09,brass);a.mesh(root,new T.TorusGeometry(.24,.055,6,24),brass,[0,-2.53,.1]);
 a.clockHands={};
 function hand(name,length,width,z,mat){const g=new T.Group();g.position.z=z;root.add(g);const shape=new T.Shape();shape.moveTo(-width*.48,-.25);shape.lineTo(-width*.6,length*.62);shape.lineTo(0,length);shape.lineTo(width*.6,length*.62);shape.lineTo(width*.48,-.25);shape.closePath();a.mesh(g,new T.ExtrudeGeometry(shape,{depth:.025,bevelEnabled:false}),mat);a.clockHands[name]=g;}
 hand('hour',1.15,.14,.40,ink);hand('minute',1.74,.10,.45,ink);hand('second',1.89,.029,.50,red);a.mesh(root,new T.SphereGeometry(.105,12,8),brass,[0,0,.57]);updateWorkshopClock(a.clockHands);return root;
}
export function updateWorkshopClock(hands,date=new Date()){if(!hands)return;const angles=clockAngles(date);for(const key of ['hour','minute','second'])hands[key].rotation.z=angles[key];}
