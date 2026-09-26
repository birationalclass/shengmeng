// Original simplified schematics of arXiv:2609.12750v1, §§ 2, 3, 5, 7.
// Blue/red always mean even/odd; no source image is embedded.
export function duanDiagram(kind,math){
 const ink='#eee9d5',blue='#8fd6ee',red='#f2a5aa',gold='#e4cf9c';
 const label=(t,x,y,size=25)=>math(t,x,y,size);
 const line=(d,c=ink,dash='')=>`<path d="${d}" fill="none" stroke="${c}" stroke-width="2.5" stroke-linecap="round"${dash?' stroke-dasharray="'+dash+'"':''}/>`;
 const dot=(x,y,c=ink,r=5)=>`<circle cx="${x}" cy="${y}" r="${r}" fill="${c}"/>`;
 const head=(x,y,d,c)=>line(`M${x-9*d} ${y-5}L${x} ${y}L${x-9*d} ${y+5}`,c);
 let out='';
 if(kind==='superstrip'){
  out=line('M115 270V48M355 270V48',blue)+line('M115 177L355 142',gold,'8 6');
  out+=dot(115,177,red)+dot(355,142,ink)+label('a',235,180)+label('\\alpha',82,175)+label('\\beta',390,140);
  out+=label('i',88,257)+label('j',380,257)+label('k',88,62)+label('l',380,62);
  out+=label('\\mathcal H_{ij}\\longrightarrow\\mathcal H_{kl}',237,302,23);
 }else if(kind==='q-solitons'){
  out=dot(100,160)+dot(380,160)+label('|I\\rangle',65,160)+label('|W\\rangle',425,160);
  for(const [bend,c,dir] of [[-132,blue,1],[-66,red,1],[66,blue,-1],[132,red,-1]]){
   const y=160+Math.sign(bend)*9;
   out+=line(`M112 ${y} Q240 ${160+bend} 368 ${y}`,c);
   // Put the arrow at the horizontal tangent so its direction stays legible.
   out+=head(240,160+bend/2+Math.sign(bend)*4.5,dir,c);
  }
  out+=label('\\mathcal R_2',240,30,30)+label('\\bar0',210,274,22)+line('M148 274H180',blue)+label('\\bar1',332,274,22)+line('M270 274H302',red);
 }else if(kind==='graded-vacua'){
  out=line('M35 249H452M48 263V38')+head(452,249,1,ink)+label('\\phi',454,279)+label('V',29,34);
  // Schematic multiwell shape: heights carry no numerical claim.
  out+=line('M73 89Q77 249 88 249C111 249 111 64 130 83C151 100 143 249 167 249C190 249 187 166 211 166C234 166 226 249 246 249C270 249 269 83 290 83C311 83 303 249 325 249C349 249 348 64 367 83C385 100 383 249 404 249L416 89',gold);
  [88,167,246,325,404].forEach((x,i)=>{out+=dot(x,249,i%2?red:blue,6)+label(String(i),x,280,20);});
  out+=label('\\mathcal{SM}_{6,8}^{\\rm def}',247,34,28);
 }else if(kind==='boundary-symtft'){
  out=line('M60 108L166 54H412V224L306 278H60ZM60 108H306V278M306 108L412 54M166 54V224H412M60 278L166 224',blue);
  out+=line('M110 130L356 76',gold,'6 6')+dot(110,130)+dot(356,76)+label('\\rho',235,83);
  out+=label('B_{\\rm sym}',104,306,23)+label('B_{\\rm phys}',383,258,23)+label('B^*_{\\rm sym}',247,25,24);
  out+=label('\\lambda_{ij}',97,91,20)+label('\\widetilde{\\mathcal O}_{ij}',394,110,20)+label('\\mathcal Z(\\mathscr C)',253,185,30);
 }else return null;
 return `<svg xmlns="http://www.w3.org/2000/svg" width="480" height="320" viewBox="0 0 480 320">${out}</svg>`;
}
