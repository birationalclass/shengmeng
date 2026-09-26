// Original schematics of constructions discussed in KM98, not scanned book figures.
export function kmDiagram(kind,math){
 if(!kind.startsWith('km-'))return null;
 const ink='#eee9d5',gold='#e4cf9c',blue='#a5dbcf';
 const label=(t,x,y,size=25)=>math(t,x,y,size);
 const line=(x,y,u,v,color=ink)=>`<path d="M${x} ${y}L${u} ${v}" stroke="${color}" stroke-width="2.5" fill="none"/>`;
 const arrow=(x,y,u,v,color=ink)=>{const a=Math.atan2(v-y,u-x);return line(x,y,u,v,color)+line(u,v,u-12*Math.cos(a-.4),v-12*Math.sin(a-.4),color)+line(u,v,u-12*Math.cos(a+.4),v-12*Math.sin(a+.4),color);};
 let out='';
 if(kind==='km-ade'){
  const pts=[[60,95],[140,95],[220,95],[300,95],[380,95]];
  for(let i=1;i<pts.length;i++)out+=line(...pts[i-1],...pts[i]);
  for(const [x,y] of pts)out+=`<circle cx="${x}" cy="${y}" r="6" fill="${gold}"/>`+label('-2',x,y+40,22);
  out+=label('A_5',225,38,30);
  out+=line(105,246,205,246)+line(205,246,305,246)+line(305,246,365,192)+line(305,246,365,300);
  for(const [x,y] of [[105,246],[205,246],[305,246],[365,192],[365,300]])out+=`<circle cx="${x}" cy="${y}" r="6" fill="${blue}"/>`;
  out+=label('D_5',60,246,30);
 }else if(kind==='km-flop'){
  out+=label('X',70,60,35)+label('X^+',405,60,35)+label('Z',240,260,35);
  out+=arrow(92,90,215,226)+arrow(385,90,265,226)+line(115,60,355,60,gold);
  out+=label('f',120,172,26)+label('f^+',358,172,26)+label(String.raw`D\cdot C<0`,86,282,20)+label(String.raw`D^+\cdot C^+>0`,389,282,20);
 }else if(kind==='km-blowup'){
  out+=line(35,68,183,244,gold)+line(35,244,183,68,blue)+`<circle cx="109" cy="156" r="5" fill="${ink}"/>`;
  out+=label('p',131,157)+label('L',37,49)+label('H',189,49);
  out+=arrow(206,160,260,160);
  out+=line(293,75,455,75,gold)+line(293,237,455,237,blue)+`<ellipse cx="375" cy="156" rx="34" ry="81" fill="none" stroke="${ink}" stroke-width="2.5"/>`;
  out+=label('E',428,156)+label("L'",307,49)+label("H'",307,275)+label('a(E)=-1',366,312,22);
 }else if(kind==='km-resolution'){
  out+=label('W',235,45,35)+label('X',65,269,35)+label("X'",410,269,35);
  out+=arrow(215,77,86,225)+arrow(260,77,388,225)+line(110,266,357,266,gold);
  out+=label('p',117,149)+label('q',354,149);
 }
 return `<svg xmlns="http://www.w3.org/2000/svg" width="480" height="320" viewBox="0 0 480 320">${out}</svg>`;
}
