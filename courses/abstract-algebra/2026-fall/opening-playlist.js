/* A complete shuffled deck per cycle, with reproducible reverse playback. */
(function(host){
  'use strict';
  function create({sceneIds,randomized=false,seed=0}){
    const ids=[...sceneIds];
    if(!ids.length||new Set(ids).size!==ids.length)throw new RangeError('Select distinct scenes');
    function order(cycle=0){
      const result=[...ids];if(!randomized)return result;
      let state=(seed^Math.imul(cycle+1,0x9e3779b9))>>>0;
      const random=()=>{state+=0x6d2b79f5;let t=state;t=Math.imul(t^t>>>15,t|1);t^=t+Math.imul(t^t>>>7,t|61);return ((t^t>>>14)>>>0)/4294967296;};
      for(let i=result.length-1;i>0;i--){const j=Math.floor(random()*(i+1));[result[i],result[j]]=[result[j],result[i]];}
      return result;
    }
    return Object.freeze({order,randomized,sceneIds:[...ids]});
  }
  host.CourseOpeningPlaylist=Object.freeze({create});
})(typeof window!=='undefined'?window:globalThis);
