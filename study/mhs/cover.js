// Adapted directly from spectral/boot.js: preserve the full shaped glyph layout.
export function createCover({overlay,english,reduced,enabled,font}) {
 let stopTitleEntrance=()=>{},entranceRequest=0,coverFont=font(),lastLanguage=null;
 const animateTitle=async()=>{
  const request=++entranceRequest;stopTitleEntrance();
  const title=overlay.querySelector('.loader-title'),face=title.querySelector(':scope > .loader-title-face');
  if(!face||reduced()||!enabled()||!Element.prototype.animate)return;
  overlay.classList.add('cover-intro');title.classList.add('is-assembling');
  if(coverFont==='c'&&title.lang==='zh-CN'){
   try{await document.fonts.load('96px "Cover Ma Shan Zheng"',face.textContent);}catch{}
   if(request!==entranceRequest)return;
  }
  const bounds=title.getBoundingClientRect(),text=face.firstChild;
  const starts=[];let offset=0;
  for(const glyph of Array.from(text.textContent)){
   const range=document.createRange();range.setStart(text,offset);offset+=glyph.length;range.setEnd(text,offset);
   if(glyph.trim())starts.push(range.getBoundingClientRect().left-bounds.left);
  }
  const letters=starts.map((start,index)=>{
   const letter=document.createElement('span');letter.className='loader-title-letter';letter.setAttribute('aria-hidden','true');
   // These bands partition one full text layout, including tracking, kerning and shadows.
   const left=index===0?-.12*parseFloat(getComputedStyle(title).fontSize):start;
   const right=index===starts.length-1?bounds.width+.12*parseFloat(getComputedStyle(title).fontSize):starts[index+1];
   letter.style.clipPath=`inset(-.12em ${bounds.width-right}px -.12em ${left}px)`;
   for(const name of ['loader-title-depth','loader-title-face'])letter.append(title.querySelector(`:scope > .${name}`).cloneNode(true));
   return letter;
  });
  overlay.classList.add('cover-intro');title.classList.add('is-assembling');title.append(...letters);
  let settled=false,disposed=false;
  // Keep the settled bands: no last-frame switch between composited and static text.
  const finish=()=>{if(settled||disposed)return;settled=true;title.classList.replace('is-assembling','is-assembled');overlay.classList.remove('cover-intro');};
  const animations=letters.map(letter=>{
   const distance=(Math.random()<.5?-1:1)*(55+Math.random()*Math.min(170,innerHeight*.2));
   return letter.animate([{transform:`translateY(${distance}px)`,opacity:0},{transform:'none',opacity:1}],
    {duration:1300+Math.random()*500,delay:Math.random()*320,easing:'cubic-bezier(.16,1,.3,1)',fill:'both'});
  });
  // A resize/fullscreen transition must immediately restore the responsive title.
  const cancel=()=>{if(disposed)return;disposed=true;animations.forEach(animation=>animation.cancel());letters.forEach(letter=>letter.remove());title.classList.remove('is-assembling','is-assembled');overlay.classList.remove('cover-intro');window.removeEventListener('resize',cancel);stopTitleEntrance=()=>{};};
  stopTitleEntrance=cancel;
  window.addEventListener('resize',cancel,{once:true});
  Promise.all(animations.map(animation=>animation.finished)).then(finish,finish);
 };

 function sync(){
  const en=english(),title=overlay.querySelector('.loader-title'),author=overlay.querySelector('.loader-author');
  const changed=lastLanguage!==en||coverFont!==font();
  if(changed){++entranceRequest;stopTitleEntrance();coverFont=font();overlay.dataset.coverFont=coverFont;
   title.lang=author.lang=en?'en':'zh-CN';
   for(const part of title.querySelectorAll(':scope>.loader-title-face,:scope>.loader-title-depth'))part.textContent=en?'Mixed Hodge Structure':'混合 Hodge 结构';
   author.textContent=en?'Sheng Meng':'孟晟';lastLanguage=en;
   if(!overlay.hidden)play();
  }
 }
 function stop(){++entranceRequest;stopTitleEntrance();overlay.classList.remove('cover-intro');}
 function play(){if(reduced()||!enabled()){stop();return;}animateTitle();}
 return {sync,play,stop};
}
