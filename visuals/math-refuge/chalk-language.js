// Translations of the existing notebook's captions; formula TeX is unchanged.
const basics=[
['A double complex, two differentials','Each node is a vector space, not a vector. Horizontal arrows raise the first degree; vertical arrows raise the second. The two composites are negatives of one another.'],
['Total degree: a diagonal direct sum','In the first quadrant each diagonal has finitely many terms. Both differentials raise total degree by one.'],
['Filtration: part of a diagonal','Keep the terms of total degree n with first index at least p, ending at (n,0). Increasing p removes the leftmost term.'],
['E0: form the quotient first','The quotient removes components with first index greater than p. Projection to column p gives the natural isomorphism; no complement is chosen.'],
['The zeroth page','For the column filtration, the zeroth page is naturally the vertical complex.'],
['A spectral sequence','The data include all pages, their differentials, and the structure isomorphisms obtained by taking cohomology.'],
['General pages: filtered quotients','Each page is a quotient in the original filtered complex. Its differential is induced by D.'],
['Filtered cycles and boundaries','Define cycles and boundaries in the original filtered complex first, then construct the pages.']
];
const convergence=[
['Page cohomology and stabilization','The first-quadrant condition eventually makes both incoming and outgoing differentials zero at a fixed position. Later pages are naturally isomorphic.'],
['The stable term','Use the natural isomorphisms from the preceding statement to denote the stable term.'],
['The induced cohomology filtration','Take the images in total cohomology of the inclusions of the filtered subcomplexes.'],
['Convergence','Convergence, the convergence of the total complex, initial-page notation, and degeneration.']
];
const hodge=['Complex differential forms','The Dolbeault double complex','The Hodge-de Rham spectral sequence','The Hodge filtration','The dd-bar lemma and degeneration','Closed representatives and canonical splitting','Hodge decomposition'];
const leray=['Geometric setup','Injective resolutions','The direct-image complex','Boundaries, cycles and cohomology sheaves','Auxiliary injective resolutions','The horseshoe lemma and termwise construction','Cartan-Eilenberg resolutions','Global sections','Differentials and sign conventions','The total complex and column filtration','The second page of the Leray sequence','Identifying total cohomology','Leray convergence','Application: vanishing of higher direct images','Application: rational singularities'];
export function chalkCopy(page,language='zh'){
  if(language!=='en')return {title:page.title,text:page.text,source:page.source};
  let entry,source=page.source;
  if(source.startsWith('基础 ')){const i=Number(source.split(' ')[1]);entry=basics[i-1];source='Foundations '+i;}
  else if(source==='总上同调'){entry=['First take total cohomology','Since D squared is zero, every boundary is a cycle. The quotient is well defined. The spectral sequence then describes the associated graded of total cohomology.'];source='Total cohomology';}
  else if(source.startsWith('收敛 ')){const i=Number(source.split(' ')[1]);entry=convergence[i-1];source='Convergence '+i;}
  else if(source.startsWith('Hodge ')){const i=Number(source.split('.')[1]);entry=[hodge[i-1],i>=5?'Assume X is compact Kahler. The canonical splitting uses the additional dd-bar condition.':'Let X be a compact complex manifold. The stable page of the column filtration identifies the associated graded of total cohomology.'];}
  else if(source.startsWith('Leray ')){const i=Number(source.split('.')[1]);entry=[leray[i-1],i===14?'In characteristic zero, take a projective birational morphism with X smooth; apply the vanishing theorem in the notes.':i===15?'In characteristic zero, let X be normal and let pi be a resolution. See the original notes for all hypotheses and proofs.':'Let f: X to Y be a morphism of schemes. Take injective resolutions in the category of module sheaves. See the original notes for the full construction.'];}
  if(!entry)throw new Error('Missing English chalk caption: '+page.source);
  return {title:entry[0],text:entry[1],source};
}

export function wrapChalkText(ctx,text,width){
  const words=/[\u3400-\u9fff]/.test(text)?[...text]:text.split(/(\s+)/),lines=[];let line='';
  for(const word of words){if(line&&ctx.measureText(line+word).width>width){lines.push(line.trim());line=word.trimStart();}else line+=word;}
  if(line.trim())lines.push(line.trim());return lines;
}

export function composeChalkPage(ctx,page,index,language,formula){
  const copy=chalkCopy(page,language),font=language==='en'?'RefugeLatin, cursive':'RefugeChinese, Kaiti SC, serif',rows=[];
  ctx.clearRect(0,0,1536,640);ctx.fillStyle='#eee9d5';ctx.textBaseline='alphabetic';
  function textRow(text,x,y,size,color){
    ctx.font=`${size}px ${font}`;
    while(ctx.measureText(text).width>1368&&size>24)ctx.font=`${--size}px ${font}`;
    ctx.fillStyle=color;ctx.fillText(text,x,y);const metrics=ctx.measureText(text);
    rows.push([x-4,y-size-4,Math.min(1376,metrics.width+8),size+14]);
  }
  textRow(copy.title,84,75,58,'#e4cf9c');textRow(copy.source+' · '+(index+1),88,123,30,'#aac8b9');
  const [x,y,w,h]=page.rows[2];ctx.drawImage(formula,x+8,y+8,w-16,h-16);rows.push([x,y,w,h]);
  ctx.font=`42px ${font}`;const notes=wrapChalkText(ctx,copy.text,1344);
  notes.slice(0,3).forEach((line,i)=>textRow(line+(i===2&&notes.length>3?' …':''),88,463+i*46,42,'#eee9d5'));
  ctx.font=`25px ${font}`;ctx.fillStyle='#9dbbab';ctx.fillText((language==='en'?'Sheng Meng · Spectral sequence notes / ':'孟晟 · 谱序列学习笔记 / ')+(index+1),88,611);
  return rows;
}
