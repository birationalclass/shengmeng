/* Fonts are part of the opening's load barrier, including any canvas lettering. */
(() => {
  'use strict';
  const base=new URL('.',document.currentScript.src);
  const definitions=Object.freeze([
    ['OpeningSerif','fonts/OpeningSerif-Regular.woff2','normal','400'],
    ['OpeningSerif','fonts/OpeningSerif-Italic.woff2','italic','400'],
    ['OpeningSans','fonts/OpeningSans.woff2','normal','100 900'],
    ['OpeningChinese','fonts/OpeningChinese-Regular.woff2','normal','400'],
    ['OpeningCopperplate','fonts/PinyonScript-Regular.ttf','normal','400'],
    ['OpeningMath','../../../visuals/chaos/fonts/STIXTwoMath.otf','normal','400']
  ].map(Object.freeze));
  const faces=new Map();let pending=null,attempt=0;
  function prepare(onProgress=()=>{}){
    if(pending)return pending;
    const current=++attempt;
    pending=(async()=>{
      if(!document.fonts||typeof FontFace!=='function')throw new Error('Font loading is unavailable');
      let completed=0,timer;
      const jobs=definitions.map(([family,path,style,weight],index)=>{
        let face=faces.get(index);
        if(!face||face.status!=='loaded'){
          if(face)document.fonts.delete(face);
          const url=new URL(path,base);
          // A fresh request can recover from a failed or timed-out font response.
          if(current>1)url.searchParams.set('font-retry',String(current));
          face=new FontFace(family,`url("${url.href}")`,{style,weight,display:'swap'});
          faces.set(index,face);
        }
        return face.load().then(loaded=>{
          document.fonts.add(loaded);completed++;
          if(current===attempt)onProgress(completed/definitions.length);
        });
      });
      try{
        await Promise.race([
          Promise.all(jobs),
          new Promise((_,reject)=>{timer=setTimeout(()=>reject(new Error('Font loading timed out')),25000);})
        ]);
      }finally{clearTimeout(timer);}
      if([...faces.values()].some(face=>face.status!=='loaded'))throw new Error('A required opening font is missing');
      return true;
    })().catch(error=>{if(current===attempt)pending=null;error.fontLoading=true;throw error;});
    return pending;
  }
  window.CourseOpeningFonts=Object.freeze({prepare,definitions});
})();
