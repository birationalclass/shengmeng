import {watchPageActivity} from './page-activity.mjs?v=nebula-70';
// Equal element orders always sound alike, across galaxies and attempts.
export function birthFrequency(order=1){
 const n=Number.isInteger(order)&&order>0?order:1;
 const steps=[0,2,4,7,9],index=Math.min(14,n-1);
 return 261.625565*Math.pow(2,(12*Math.floor(index/5)+steps[index%5])/12);
}
// Original synthesised glass/metal entry chime; no proprietary game sample.
export function createChallengeAudio(){let ctx,enabled=true;const muted=new URLSearchParams(location.search).get('mute')==='1';
 let active=true;watchPageActivity(value=>{active=value;if(ctx){if(value)void ctx.resume();else void ctx.suspend();}});
 function sound(kind,order=1){let music;try{music=JSON.parse(localStorage.getItem('generators-endless-music')||'null');}catch{}if(!active||muted||!enabled||music?.enabled===false)return;try{ctx??=new (window.AudioContext||window.webkitAudioContext)();void ctx.resume();const now=ctx.currentTime,notes=kind==='enter'?[196,294,392,587]:kind==='success'?[262,330,392,524]:kind==='fail'?[130,98,65]:kind==='birth'?[birthFrequency(order)]:[440,660];notes.forEach((hz,i)=>{const o=ctx.createOscillator(),g=ctx.createGain();o.type=kind==='fail'?'triangle':'sine';o.frequency.setValueAtTime(hz,now+i*.085);if(kind==='fail')o.frequency.exponentialRampToValueAtTime(hz*.45,now+1.1);g.gain.setValueAtTime(0,now+i*.085);g.gain.linearRampToValueAtTime(kind==='birth'?.025:.075,now+i*.085+.012);g.gain.exponentialRampToValueAtTime(.0001,now+i*.085+(kind==='enter'?1.9:.85));o.connect(g).connect(ctx.destination);o.onended=()=>{o.disconnect();g.disconnect();};o.start(now+i*.085);o.stop(now+i*.085+2);});}catch{}}
 return {sound,setEnabled(v){enabled=v;}};
}
