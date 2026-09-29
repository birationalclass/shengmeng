import {watchPageActivity} from './page-activity.mjs?v=nebula-70';
// A pentatonic phrase keeps successive births distinct without harsh interval jumps.
export function createBirthMelody(random=Math.random){
 const scale=[392,440,523.251,587.330,659.255,783.991];let previous=2;
 return ()=>{const candidates=[-2,-1,1,2].map(step=>previous+step).filter(i=>i>=0&&i<scale.length);previous=candidates[Math.min(candidates.length-1,Math.floor(random()*candidates.length))];return scale[previous];};
}
// Original synthesised glass/metal entry chime; no proprietary game sample.
export function createChallengeAudio(){let ctx,enabled=true;const nextBirthNote=createBirthMelody();const muted=new URLSearchParams(location.search).get('mute')==='1';
 let active=true;watchPageActivity(value=>{active=value;if(ctx){if(value)void ctx.resume();else void ctx.suspend();}});
 function sound(kind){let music;try{music=JSON.parse(localStorage.getItem('generators-endless-music')||'null');}catch{}if(!active||muted||!enabled||music?.enabled===false)return;try{ctx??=new (window.AudioContext||window.webkitAudioContext)();void ctx.resume();const now=ctx.currentTime,notes=kind==='enter'?[196,294,392,587]:kind==='success'?[262,330,392,524]:kind==='fail'?[130,98,65]:kind==='birth'?[nextBirthNote()]:[440,660];notes.forEach((hz,i)=>{const o=ctx.createOscillator(),g=ctx.createGain();o.type=kind==='fail'?'triangle':'sine';o.frequency.setValueAtTime(hz,now+i*.085);if(kind==='fail')o.frequency.exponentialRampToValueAtTime(hz*.45,now+1.1);g.gain.setValueAtTime(0,now+i*.085);g.gain.linearRampToValueAtTime(kind==='birth'?.025:.075,now+i*.085+.012);g.gain.exponentialRampToValueAtTime(.0001,now+i*.085+(kind==='enter'?1.9:.85));o.connect(g).connect(ctx.destination);o.onended=()=>{o.disconnect();g.disconnect();};o.start(now+i*.085);o.stop(now+i*.085+2);});}catch{}}
 return {sound,setEnabled(v){enabled=v;}};
}
