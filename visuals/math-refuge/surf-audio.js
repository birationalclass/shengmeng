import {shoreDistance,surfGain} from './coastal-site.js?v=true-north-coast-1';
// Same filtered brown-noise source as Ocean Study. The host adds distance gain.
export function createSurfAudio(){
 let context,source,filter,gain,enabled=false,lastDistance=100,elapsed=0;
 const mute=()=>{if(gain)gain.gain.setTargetAtTime(0,context.currentTime,.25);};
 document.addEventListener('visibilitychange',()=>{if(document.hidden)mute();});
 return {
  async setEnabled(value){
   if(value&&!context){const Audio=window.AudioContext||window.webkitAudioContext;if(!Audio)throw new Error('当前浏览器不支持海浪声音');context=new Audio();
    const buffer=context.createBuffer(1,context.sampleRate*12,context.sampleRate),channel=buffer.getChannelData(0);let brown=0;
    for(let i=0;i<channel.length;i++){brown=(brown+Math.random()*.04-.02)/1.02;channel[i]=brown*3.5;}
    source=context.createBufferSource();source.buffer=buffer;source.loop=true;filter=context.createBiquadFilter();filter.type='lowpass';filter.frequency.value=1250;gain=context.createGain();gain.gain.value=0;source.connect(filter).connect(gain).connect(context.destination);source.start();
   }
   if(value)await context.resume();enabled=value;if(!value)mute();
  },
  update(position,time,dt){if(!gain)return;elapsed+=dt;if(elapsed>.15){lastDistance=shoreDistance(position);elapsed=0;}
   const volume=enabled&&!document.hidden?surfGain(lastDistance)*(.65+.35*Math.sin(time*.88)):0;
   gain.gain.setTargetAtTime(volume,context.currentTime,.6);filter.frequency.setTargetAtTime(450+800/(1+lastDistance/40),context.currentTime,.6);
  },
  dispose(){mute();source?.stop();context?.close();}
 };
}
