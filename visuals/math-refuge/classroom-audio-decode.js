// Transfer compressed audio, then materialize PCM locally before media playback.
// The compressed course cache stays small; callers retain PCM URLs only for
// the current/next board. No live output device is opened for offline decoding.
let decoder=null,completed=0,active=0,last=null;
export function pcmWavBlob(buffer){
 const channels=buffer.numberOfChannels,frames=buffer.length,bytes=frames*channels*2;
 if(!channels||channels>8||bytes>0xffffffff-36)throw Error('语音格式或长度不受支持');
 const raw=new ArrayBuffer(44+bytes),view=new DataView(raw),text=(at,s)=>{for(let i=0;i<s.length;i++)view.setUint8(at+i,s.charCodeAt(i));};
 text(0,'RIFF');view.setUint32(4,36+bytes,true);text(8,'WAVE');text(12,'fmt ');view.setUint32(16,16,true);view.setUint16(20,1,true);view.setUint16(22,channels,true);view.setUint32(24,buffer.sampleRate,true);view.setUint32(28,buffer.sampleRate*channels*2,true);view.setUint16(32,channels*2,true);view.setUint16(34,16,true);text(36,'data');view.setUint32(40,bytes,true);
 const data=Array.from({length:channels},(_,i)=>buffer.getChannelData(i));
 for(let i=0,at=44;i<frames;i++)for(let c=0;c<channels;c++,at+=2){const x=Math.max(-1,Math.min(1,data[c][i]));view.setInt16(at,Math.round(x*(x<0?32768:32767)),true);}
 return new Blob([raw],{type:'audio/wav'});
}
export async function prepareClassroomAudioBlob(blob,{expectedSeconds}={}){
 const header=new Uint8Array(await blob.slice(0,12).arrayBuffer());
 if(header[0]===82&&header[1]===73&&header[2]===70&&header[3]===70&&header[8]===87&&header[9]===65&&header[10]===86&&header[11]===69)return blob;
 const Offline=globalThis.OfflineAudioContext||globalThis.webkitOfflineAudioContext;
 if(!Offline)throw Error('浏览器不支持语音预解码，请使用本机WAV版本');
 decoder ||=new Offline(1,1,48000);active++;
 try{
  const buffer=await decoder.decodeAudioData(await blob.arrayBuffer());
  if(Number.isFinite(expectedSeconds)&&Math.abs(buffer.duration-expectedSeconds)>.05)throw Error('语音解码时长与板书时间轴不一致');
  const pcm=pcmWavBlob(buffer);completed++;last={networkBytes:blob.size,pcmBytes:pcm.size,duration:buffer.duration,sampleRate:buffer.sampleRate,channels:buffer.numberOfChannels};return pcm;
 }finally{active--;}
}
export function classroomAudioDecodeState(){return{completed,active,last};}
