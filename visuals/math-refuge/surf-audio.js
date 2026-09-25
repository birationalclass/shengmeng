import {shoreDistance,surfGain} from './coastal-site.js?v=true-north-coast-1';
// CC0 stereo field recording + a very quiet low-frequency swell bed.
export function createSurfAudio(){
 let context,source,filter,gain,recording,mediaGain,enabled=false,lastDistance=100,elapsed=0,revision=0;
 const mute=()=>{if(gain)gain.gain.setTargetAtTime(0,context.currentTime,.25);recording?.pause();};
 const visibility=()=>{if(document.hidden)mute();else if(enabled){context?.resume();recording?.play().catch(()=>{});}};
 document.addEventListener('visibilitychange',visibility);
 return {
  async setEnabled(value){
   const token=++revision;enabled=Boolean(value);
   if(value&&!context){const AudioContext=window.AudioContext||window.webkitAudioContext;if(!AudioContext)throw new Error('当前浏览器不支持海浪声音');context=new AudioContext();
    const buffer=context.createBuffer(1,context.sampleRate*19,context.sampleRate),channel=buffer.getChannelData(0);let brown=0;
    for(let i=0;i<channel.length;i++){brown=(brown+Math.random()*.04-.02)/1.02;channel[i]=brown*3.5;}
    source=context.createBufferSource();source.buffer=buffer;source.loop=true;filter=context.createBiquadFilter();filter.type='lowpass';filter.frequency.value=1250;gain=context.createGain();gain.gain.value=0;
    const bed=context.createGain();bed.gain.value=.22;source.connect(bed).connect(filter).connect(gain).connect(context.destination);source.start();
    recording=new Audio(new URL('./assets/audio/shore-waves-glm-kg.mp3',import.meta.url).href);recording.loop=true;recording.preload='none';
    mediaGain=context.createGain();mediaGain.gain.value=.24;context.createMediaElementSource(recording).connect(mediaGain).connect(filter);
   }
   if(value){await context.resume();if(token===revision&&enabled)await recording.play().catch(()=>{});}else mute();
  },
  update(position,time,dt){if(!gain)return;elapsed+=dt;if(elapsed>.15){lastDistance=shoreDistance(position);elapsed=0;}
   // Half of the previous distance-dependent master level, in every scene state.
   const volume=enabled&&!document.hidden?surfGain(lastDistance)*.5:0;
   gain.gain.setTargetAtTime(volume,context.currentTime,.6);filter.frequency.setTargetAtTime(650+4200/(1+lastDistance/40),context.currentTime,.6);
  },
  dispose(){enabled=false;revision++;mute();source?.stop();context?.close();document.removeEventListener('visibilitychange',visibility);}
 };
}
