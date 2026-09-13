/* A reversible biography in seven sand tableaux. Dates and words follow the sand. */
(function(host){
  'use strict';
  const nodes=[
    {year:'1811–1832',title:'ÉVARISTE GALOIS',zhTitle:'短暂的生命，无尽的回响',en:'Twenty years of life.\nAn idea that changed algebra.',zh:'二十年的生命，\n改变代数的思想。'},
    {year:'1827',title:'AWAKENING',zhTitle:'少年与数学',en:'A book opens.\nA new mathematical world takes shape.',zh:'少年走进数学。\n书页展开，一个新的世界随之成形。'},
    {year:'1831',title:'SYMMETRIES OF ROOTS',zhTitle:'根的对称',kind:'galois-theorem',en:'GALOIS’S SOLVABILITY CRITERION\n\nSolvable by radicals\n⇔ Gal(f) is solvable\n\nFor polynomials over ℚ.\nModern formulation.',zh:'伽罗瓦可解性判据\n\n根式可解\n⇔ Gal(f) 是可解群\n\n有理系数多项式 · 现代表述'},
    {year:'1831',title:'BEHIND BARS',zhTitle:'囚窗之内',en:'His memoir was returned without approval.\nPolitical turmoil brought imprisonment.\n\nBehind bars, his ideas endured.',zh:'论文未获认可，\n政治风暴又将他带入牢狱。\n\n窗栅之内，思想仍在追寻。'},
    {year:'29 MAY 1832',title:'A LETTER TO THE FUTURE',zhTitle:'留下思想',en:'Before the duel, he set down his research\nin a letter to his friend Auguste Chevalier.\n\nYears of thought, entrusted to the future.',zh:'决斗前，他将已有研究写进\n致友人奥古斯特·舍瓦利耶的信。\n\n积累的思想，被托付给未来。'},
    {year:'30–31 MAY 1832',title:'TWENTY YEARS',zhTitle:'二十岁',en:'Wounded in a duel on May 30.\nHe died on May 31, aged twenty.\n\nA brief life ends.\nThe ideas remain.',zh:'5 月 30 日决斗受伤，\n31 日离世，年仅二十岁。\n\n生命止息，思想留存。'},
    {year:'1843 → 1846',title:'THE ECHO',zhTitle:'回响',en:'The manuscripts wait.\nYears pass in silence.',zh:'手稿留存。\n岁月在沉寂中流逝。'}
  ].map(item=>Object.freeze({kind:'galois-history',...item}));
  const recognition=Object.freeze({kind:'galois-history',en:'1843 · Liouville recognizes the work.\n1846 · The manuscripts are published.',zh:'1843 年，刘维尔读懂了手稿。\n1846 年，手稿刊行，思想传世。'});
  // The 177.160612-second album cut. Cue points follow measured musical
  // dynamics: 23.75 rise, 70.05 fall, 92.55 rise, 124.55 fall, 166.15 final peak.
  const score=Object.freeze({duration:177160.612,track:'The Great Eagle',artist:'Bear McCreary',
    starts:Object.freeze([0,11000,24000,70000,92500,124550,143000]),
    holdEnds:Object.freeze([7000,18000,64000,86500,117500,133500,177160.612]),
    finalPeak:166150});
  function layout(hold,morph,scored=false){
    const starts=scored?score.starts:nodes.map((_,i)=>i*(hold+morph));
    const ends=scored?score.holdEnds:starts.map(t=>t+hold);
    return {starts,ends,duration:ends[ends.length-1]};
  }
  function duration(hold,morph,scored=false){return scored?score.duration:nodes.length*hold+(nodes.length-1)*morph;}
  function state(elapsed,hold,morph,scored=false){
    const plan=layout(hold,morph,scored),position=Math.max(0,Math.min(plan.duration,elapsed));
    let from=0;while(from<nodes.length-1&&position>=plan.starts[from+1])from++;
    const moving=from<nodes.length-1&&position>=plan.ends[from],holdDuration=plan.ends[from]-plan.starts[from];
    return {from,to:moving?from+1:from,node:from,moving,progress:moving?Math.min(1,(position-plan.ends[from])/(plan.starts[from+1]-plan.ends[from])):1,
      holdElapsed:Math.min(holdDuration,position-plan.starts[from]),holdDuration,position};
  }
  function remap(elapsed,oldHold,oldMorph,hold,morph,oldScored=false,scored=false){
    const s=state(elapsed,oldHold,oldMorph,oldScored),plan=layout(hold,morph,scored);
    return s.moving?plan.ends[s.from]+s.progress*(plan.starts[s.to]-plan.ends[s.from]):plan.starts[s.from]+s.holdElapsed/s.holdDuration*(plan.ends[s.from]-plan.starts[s.from]);
  }
  function atNode(index,hold,morph,scored=false){const plan=layout(hold,morph,scored);return (plan.starts[index]+plan.ends[index])/2;}
  host.CourseOpeningGaloisStory=Object.freeze({nodes:Object.freeze(nodes),recognition,score,duration,state,remap,atNode});
})(typeof window!=='undefined'?window:globalThis);
