import {equationLines} from './chalk-layout.mjs';
// Editorial blocks keep a mathematical argument together. Full explanations
// are kept with their blocks and reflowed onto the physical board at render time.
export function flowBoard(pages){
 const first=pages[0];
 return {...first,annotation:undefined,diagram:null,layout:'flow',
  blocks:pages.flatMap(p=>p.blocks||[{text:p.boardCue||(p.title==='等号要求怎样的纤维'?'p_g(X)>243；等号要求的纤维':p.title),enText:p.en.boardCue||(p.title==='等号要求怎样的纤维'?'Assume p_g(X)>243; the equality fibre':p.en.title),tex:p.tex}]),
  tex:pages.map(p=>p.tex).join('\n'),text:pages.map(p=>p.text).join('\n\n'),
  en:{...first.en,text:pages.map(p=>p.en.text).join('\n\n')},
  sourcePages:pages.flatMap(p=>p.sourcePages||[{source:p.source,title:p.title}])};
}
export function organizeBoards(pages,{minimum=24}={}){
 let merges=Math.max(0,pages.filter(p=>!p.kind).length-minimum);const out=[];
 const group=p=>p.section||p.source?.split(' · ')[0];
 for(let i=0;i<pages.length;i++){
  const a=pages[i],b=pages[i+1];
  const eligible=p=>p&&!p.kind&&!p.diagram&&!p.annotation&&!p.blocks&&!p.title.startsWith('勘误');
  const sparse=p=>equationLines(p.tex).length<=2&&p.tex.length<450;
  if(merges&&eligible(a)&&eligible(b)&&group(a)===group(b)&&sparse(a)&&sparse(b)){
   out.push(flowBoard([a,b]));i++;merges--;
  }else out.push(eligible(a)?flowBoard([a]):a);
 }
 return out;
}
