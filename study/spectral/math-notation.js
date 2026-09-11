// Keep the representative on its baseline and place its space beneath it.
export function representativeIn(element,space){
 return String.raw`\underset{\substack{\vbelongs\\${space}}}{${element}}`;
}
export function renderMathematics(katex,tex,display=false){
 const html=katex.renderToString(tex,{displayMode:display,throwOnError:true,strict:'error',trust:false,macros:{'\\vbelongs':String.raw`\mathord{\in}`}});
 return tex.includes('\\vbelongs')?html.replace(/(<span class="mord(?: mtight)?"><span class="mord(?: mtight)?"><span class=")(mrel(?: mtight)?)(">∈<\/span><\/span><\/span>)/g,'$1$2 representative-membership$3'):html;
}
