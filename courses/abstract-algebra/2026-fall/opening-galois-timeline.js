/* A quiet historical scale, independent of display frame rate and playback direction. */
(function(host){
  'use strict';
  const firstYear=1811,lastYear=1846,duration=177160.612;
  const cues=Object.freeze([
    [0,1811],[7000,1811],[11000,1827],[18000,1827],
    [24000,1831],[86500,1831],[92500,1832],[143000,1832],
    [166000,1843],[168200,1843],[169000,1846],[duration,1846]
  ].map(Object.freeze));
  const states=new WeakMap();
  const clamp=(n,a,b)=>Math.max(a,Math.min(b,n));
  function sample({entering=false,elapsed=0}={}){
    const t=entering?0:clamp(Number.isFinite(elapsed)?elapsed:0,0,duration);
    let i=0;while(i<cues.length-2&&t>=cues[i+1][0])i++;
    const a=cues[i],b=cues[i+1],u=clamp((t-a[0])/(b[0]-a[0]),0,1),ease=u*u*(3-2*u);
    const year=a[1]+(b[1]-a[1])*ease;
    return{year,displayYear:Math.floor(year+1e-7),position:(year-firstYear)/(lastYear-firstYear),
      birth:!entering&&t<7000,death:!entering&&t>=124550&&t<133500,entering};
  }
  function initialize(element){
    element.innerHTML='<div class="galois-years-track" aria-hidden="true">'+
      '<div class="galois-years-line"></div><div class="galois-years-trace"></div>'+
      '<i class="galois-years-tick" style="--at:45.714286%"></i><i class="galois-years-tick" style="--at:57.142857%"></i><i class="galois-years-tick" style="--at:91.428571%"></i>'+
      '<span class="galois-years-anchor is-birth" style="--at:0%"><i></i><span><b>1811</b><small>诞生</small></span></span>'+
      '<span class="galois-years-anchor is-death" style="--at:60%"><i></i><span><b>1832</b><small>离世</small></span></span>'+
      '<span class="galois-years-anchor is-publication" style="--at:100%"><i></i><span><b>1846</b><small>刊行</small></span></span>'+
      '<span class="galois-years-head"><b>1811</b><i></i></span></div>';
    element.setAttribute('role','img');
    const state={head:element.querySelector('.galois-years-head b'),year:null,birth:element.querySelector('.is-birth'),death:element.querySelector('.is-death')};
    states.set(element,state);return state;
  }
  function update(element,{active=false,entering=false,elapsed=0}={}){
    if(!element)return;
    element.hidden=!active;
    if(!active){element.setAttribute('aria-hidden','true');return;}
    const state=states.get(element)||initialize(element),value=sample({entering,elapsed});
    element.removeAttribute('aria-hidden');
    element.classList.toggle('is-entering',entering);
    element.style.setProperty('--year-position',(value.position*100).toFixed(5)+'%');
    state.birth.classList.toggle('is-highlighted',value.birth);
    state.death.classList.toggle('is-highlighted',value.death);
    element.dataset.year=String(value.displayYear);
    if(state.year!==value.displayYear){
      state.year=value.displayYear;state.head.textContent=String(value.displayYear);
      element.setAttribute('aria-label','伽罗瓦生平时间轴，1811年至1846年；当前 '+value.displayYear+' 年。');
    }
  }
  host.CourseOpeningGaloisTimeline=Object.freeze({update,sample,cues});
})(typeof window!=='undefined'?window:globalThis);
