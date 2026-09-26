// Split only displayed equation rows. Fractions, cases and aligned subexpressions
// stay intact; each resulting rectangle is revealed before the next one starts.
export function equationLines(tex){
  const match=tex.match(/^\\begin\{(gathered|aligned|array)\}(\{[^}]*\})?([\s\S]*)\\end\{\1\}$/);
  if(!match)return [tex];
  const [,env,columns='',body]=match;let braces=0,depth=0,start=0;const rows=[];
  for(let i=0;i<body.length;i++){
    if(body.startsWith('\\begin{',i)){depth++;i=body.indexOf('}',i+7);continue;}
    if(body.startsWith('\\end{',i)){depth--;i=body.indexOf('}',i+5);continue;}
    if(body[i]==='\\'&&body[i+1]==='\\'&&depth===0&&braces===0){
      rows.push(body.slice(start,i));i++;
      if(body[i+1]==='[')i=body.indexOf(']',i+2);
      start=i+1;continue;
    }
    if(body[i]==='\\'&&/[{}]/.test(body[i+1]||'')){i++;continue;}
    if(body[i]==='{')braces++;if(body[i]==='}')braces--;
  }
  rows.push(body.slice(start));
  if(env==='gathered')return rows.flatMap(row=>equationLines(row.trim()));
  return rows.map(row=>`\\begin{${env}}${columns}${row}\\end{${env}}`);
}
