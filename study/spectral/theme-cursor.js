// Native SVG cursors keep an exact hotspot, including in fullscreen and dialogs.
// No following DOM layer, animation timer, or changes to touch input.
(()=>{
 const root=document.documentElement,input=document.getElementById('themeCursor');
 let enabled=true;
 try{enabled=localStorage.getItem('spectral-theme-cursor')!=='off';}catch{}
 function palette(){
  const style=getComputedStyle(root),ink=style.getPropertyValue('--ink').trim(),accent=style.getPropertyValue('--gold').trim(),bg=style.getPropertyValue('--bg').trim();
  const svg=body=>`url("data:image/svg+xml,${encodeURIComponent(`<svg xmlns="http://www.w3.org/2000/svg" width="32" height="32" viewBox="0 0 32 32">${body}</svg>`)}")`;
  const arrow=`<path d="M4 3v23l6-6 4 9 4-2-4-9h9Z" fill="${ink}" stroke="${bg}" stroke-width="1.6" stroke-linejoin="round"/><path d="m7 9 11 7h-7l-4 4Z" fill="${accent}"/>`;
  const hand=pressed=>`<path d="M11 16V6c0-4 5-4 5 0v7c1-2 5-2 5 1 2-2 5-1 5 2 3-1 4 1 3 5l-2 7H14L7 19c-2-3 1-5 3-3l3 3" fill="${pressed?accent:ink}" stroke="${bg}" stroke-width="1.6" stroke-linejoin="round"/><path d="M16 15v5m5-5v5m4-2v3" fill="none" stroke="${pressed?bg:accent}" stroke-width="1.3" stroke-linecap="round"/>`;
  root.style.setProperty('--theme-cursor-arrow',`${svg(arrow)} 4 3, auto`);
  root.style.setProperty('--theme-cursor-link',`${svg(hand(false))} 13 3, pointer`);
  root.style.setProperty('--theme-cursor-press',`${svg(hand(true))} 13 3, pointer`);
 }
 function sync(language=document.documentElement.lang==='en'?'en':'zh'){
  root.dataset.themeCursor=enabled?'on':'off';input.checked=enabled;
  document.getElementById('themeCursorLabel').textContent=language==='en'?'Use theme cursor':'使用配套主题指针';
  document.getElementById('themeCursorHint').textContent=language==='en'?'On by default. Turn off to use system cursors.':'默认开启；关闭后使用系统指针。';
 }
 function save(){try{localStorage.setItem('spectral-theme-cursor',enabled?'on':'off');}catch{}sync();}
 input.addEventListener('change',()=>{enabled=input.checked;save();});
 new MutationObserver(palette).observe(root,{attributes:true,attributeFilter:['data-panel-style']});
 window.spectralThemeCursor={sync,reset:()=>{enabled=true;save();}};
 palette();sync();
})();
