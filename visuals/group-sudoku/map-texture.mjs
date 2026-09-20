import * as T from '../3d/vendor/three.module.js';
// A seeded, ink-drawn terrain atlas: coast, ridges, forests, lakes and red roads.
export function illustratedMap(){
 const c=document.createElement('canvas');c.width=2560;c.height=1792;const x=c.getContext('2d');x.scale(2,2);const W=1280,H=896;let seed=9024;const r=()=>((seed=(Math.imul(seed,1664525)+1013904223)>>>0)/4294967296);
 const g=x.createRadialGradient(610,420,130,640,440,830);g.addColorStop(0,'#ddcf9c');g.addColorStop(.7,'#c1a66b');g.addColorStop(1,'#7b5b32');x.fillStyle=g;x.fillRect(0,0,W,H);
 for(let i=0;i<65000;i++){x.fillStyle=r()>.5?'#fff2b915':'#4b351e12';x.fillRect(r()*W,r()*H,.3+r()*1.5,.3+r());}
 // An irregular, doubled coastline rather than a rectangular sheet of contour lines.
 const coast=[];for(let k=0;k<180;k++){const q=k*Math.PI*2/180,rr=1+.065*Math.sin(q*9)+.025*Math.cos(q*23)+.015*(r()-.5);coast.push([640+575*Math.cos(q)*rr,445+361*Math.sin(q)*rr]);}
 function path(points,close=false){x.beginPath();points.forEach(([px,py],i)=>i?x.lineTo(px,py):x.moveTo(px,py));if(close)x.closePath();}
 path(coast,true);x.shadowColor='#4e3a22';x.shadowBlur=16;x.fillStyle='#e0d09e';x.fill();x.shadowBlur=0;x.strokeStyle='#493c27';x.lineWidth=1.3;x.stroke();
 for(const scale of [1.007,1.016,1.029]){path(coast.map(([a,b])=>[640+(a-640)*scale,445+(b-445)*scale]),true);x.lineWidth=.5;x.strokeStyle='#5e4d3070';x.stroke();}
 // Small hatch marks along the shore give the engraving its topographical edge.
 for(let k=0;k<coast.length;k+=2){const [a,b]=coast[k],q=Math.atan2(b-445,a-640);path([[a,b],[a+Math.cos(q)*5,b+Math.sin(q)*5]]);x.strokeStyle='#6a523c';x.lineWidth=.5;x.stroke();}
 function river(points,width){x.beginPath();x.moveTo(...points[0]);for(let k=1;k<points.length-1;k++){const [a,b]=points[k],[u,v]=points[k+1];x.quadraticCurveTo(a,b,(a+u)/2,(b+v)/2);}x.lineTo(...points.at(-1));x.strokeStyle='#59452d';x.lineWidth=width+1.3;x.lineJoin='round';x.stroke();x.strokeStyle='#7b9492';x.lineWidth=width;x.stroke();}
 river([[100,487],[170,454],[229,483],[276,454],[335,470],[396,450],[456,472],[518,453],[579,472],[635,450],[703,468],[769,441],[838,457],[896,435],[962,471],[1048,448],[1168,483]],4);
 river([[757,108],[726,160],[749,198],[714,247],[737,292],[707,333],[734,382],[703,468]],2.3);
 river([[379,751],[415,699],[399,641],[445,601],[423,548],[456,472]],2.6);
 function lake(cx,cy,w,h){const pts=[];for(let k=0;k<45;k++){const q=k*Math.PI*2/45,f=.8+r()*.3;pts.push([cx+Math.cos(q)*w*f,cy+Math.sin(q)*h*f]);}path(pts,true);x.fillStyle='#687f8a';x.fill();x.lineWidth=1.2;x.strokeStyle='#4f4635';x.stroke();for(let j=-2;j<3;j++){path([[cx-w*.3,cy+j*3],[cx+w*.35,cy+j*3+1]]);x.strokeStyle='#d9caa165';x.lineWidth=.4;x.stroke();}}
 lake(535,471,34,17);lake(933,452,25,13);lake(748,199,20,26);lake(399,650,17,29);
 function mountain(cx,cy,h){x.beginPath();x.moveTo(cx-h*.65,cy);x.lineTo(cx-h*.23,cy-h*.53);x.lineTo(cx,cy-h);x.lineTo(cx+h*.27,cy-h*.49);x.lineTo(cx+h*.66,cy);x.strokeStyle='#665034';x.lineWidth=.8;x.stroke();path([[cx,cy-h],[cx-h*.09,cy-h*.51],[cx+h*.10,cy-h*.26],[cx+h*.03,cy]]);x.lineWidth=.55;x.stroke();for(let j=1;j<7;j++){const t=j/8;path([[cx+h*.04,cy-h+t*h],[cx+h*.47*t,cy-h+t*h+3]]);x.lineWidth=.4;x.stroke();}}
 for(let chain=0;chain<4;chain++)for(let k=0;k<55;k++){const px=115+k*19+r()*9,py=[150,400,548,764][chain]+Math.sin(k*.23+chain)*19+r()*13;mountain(px,py,10+r()*19);}
 function pine(cx,cy,size){x.strokeStyle='#526344b0';x.lineWidth=.6;path([[cx,cy-size],[cx,cy+2]]);x.stroke();for(let k=0;k<3;k++){const y=cy-size+k*size*.28;path([[cx-size*(k+1)*.12,y+size*.37],[cx,y],[cx+size*(k+1)*.12,y+size*.37]]);x.stroke();}}
 for(let forest=0;forest<15;forest++){const cx=150+(forest%5)*245,cy=220+Math.floor(forest/5)*240;for(let k=0;k<42;k++)pine(cx+(r()-.5)*80,cy+(r()-.5)*39,5+r()*6);}
 x.setLineDash([3,3]);x.lineWidth=1.2;x.strokeStyle='#a45737a0';path([[182,596],[400,596],[620,596],[847,596],[1075,596],[1092,297],[858,297],[635,297],[406,297],[183,297]]);x.stroke();x.setLineDash([]);
 x.fillStyle='#57412c';x.textAlign='center';x.font='italic 16px Georgia';for(const [text,px,py,angle]of [['THE NORTHERN RIDGE',560,99,-.03],['River of Composition',650,508,-.02],['THE SOUTHERN MARCHES',802,807,.015],['The Jade Woods',260,205,-.05],['The Mirror Coast',1054,704,-.08]]){x.save();x.translate(px,py);x.rotate(angle);x.fillText(text,0,0);x.restore();}
 x.font='24px Atlas,Georgia';x.fillText('TERRA · ALGEBRA',640,862);x.font='10px Georgia';x.fillText('EIGHT DOMAINS OF COMPOSITION',640,880);
 x.save();x.translate(112,723);x.strokeStyle='#5c462f';for(const radius of [27,31,45]){x.beginPath();x.arc(0,0,radius,0,Math.PI*2);x.lineWidth=.7;x.stroke();}for(let k=0;k<8;k++){x.rotate(Math.PI/4);path([[0,-43],[5,-9],[0,0],[-5,-9]],true);x.fillStyle=k%2?'#a88a58':'#5c462f';x.fill();x.stroke();}x.fillStyle='#58402a';x.font='15px Georgia';x.fillText('N',0,-52);x.restore();
 x.strokeStyle='#6c512e';x.lineWidth=1;x.strokeRect(16,16,W-32,H-32);x.lineWidth=.4;x.strokeRect(23,23,W-46,H-46);
 const tex=new T.CanvasTexture(c);tex.colorSpace=T.SRGBColorSpace;tex.anisotropy=4;return tex;
}
