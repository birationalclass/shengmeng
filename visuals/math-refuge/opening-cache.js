// A short, private, in-memory WebCodecs frame cache. No files, network or quality changes.
// Every frame is independently decodable; retain at most four decoded surfaces.
export class OpeningCache {
 constructor({canvas,mobile=false,onState=()=>{},onRestore=()=>{},api=globalThis,seconds=3,fps=60}){
  Object.assign(this,{canvas,mobile,onState,onRestore,api,seconds,fps});this.state='idle';this.epoch=0;this.chunks=[];this.frames=new Map();this.bytes=0;this.peakBytes=0;this.index=0;this.nextDecode=0;this.inflight=0;this.elapsed=0;
 }
 stateTo(value){this.state=value;this.onState(value,{frames:this.chunks.length,progress:value==='ready'?100:Math.min(99,Math.floor(this.index/(this.seconds*this.fps+1)*100)),bytes:this.bytes,seconds:this.seconds,fps:this.fps,width:this.width||0,height:this.height||0,peakEncodedBytes:this.peakBytes,rawSurfaceBudget:(this.width||0)*(this.height||0)*4*5,error:this.error||null});}
 get waiting(){return ['preparing','recording','flushing','ready'].includes(this.state);}
 async start(){
  if(this.state!=='idle')return;const {VideoEncoder,VideoDecoder,VideoFrame}=this.api;
  if(!VideoEncoder||!VideoDecoder||!VideoFrame||this.canvas.width*this.canvas.height>(this.mobile?1800000:5500000)){this.stateTo('unavailable');return;}
  const token=++this.epoch;this.width=this.canvas.width;this.height=this.canvas.height;this.stateTo('preparing');
  try{
   let config;
   for(const codec of ['avc1.42002a','avc1.420034','vp8']){
    const candidate={codec,width:this.width,height:this.height,framerate:this.fps,bitrate:Math.min(80000000,Math.max(12000000,this.width*this.height*22)),latencyMode:'realtime',hardwareAcceleration:'no-preference',...(codec.startsWith('avc')?{avc:{format:'annexb'}}:{})};
    try{const [enc,dec]=await Promise.all([VideoEncoder.isConfigSupported(candidate),VideoDecoder.isConfigSupported({codec,codedWidth:this.width,codedHeight:this.height,optimizeForLatency:true})]);if(enc.supported&&dec.supported){config=enc.config;break;}}catch{}
   }
   if(token!==this.epoch)return;if(!config){this.error='No supported encoder / decoder configuration';this.abort('unavailable');return;}
   this.encoder=new VideoEncoder({output:(chunk,meta)=>{
    if(token!==this.epoch)return;this.bytes+=chunk.byteLength;this.peakBytes=Math.max(this.peakBytes,this.bytes);
    if(this.bytes>(this.mobile?12:32)*1024*1024){this.abort('memory-limit');return;}
    this.chunks.push(chunk);if(meta.decoderConfig)this.decoderConfig=meta.decoderConfig;
   },error:error=>{this.error=error.message;if(token===this.epoch)this.abort('unavailable');}});
   this.encoder.configure(config);this.config=config;this.stateTo('recording');
  }catch(error){this.error=error.message;if(token===this.epoch)this.abort('unavailable');}
 }
 capture(render){
  if(this.state!=='recording'||this.encoder.encodeQueueSize>=2)return;
  try{
   render(this.index/this.fps,this.index===0?0:1/this.fps);
   const frame=new this.api.VideoFrame(this.canvas,{timestamp:Math.round(this.index*1e6/this.fps),duration:Math.round(1e6/this.fps)});
   try{this.encoder.encode(frame,{keyFrame:true});}finally{frame.close();}
   if(this.state!=='recording')return;
   this.index++;if(this.index%6===0)this.stateTo('recording');
   if(this.index>this.seconds*this.fps){this.stateTo('flushing');const token=this.epoch;this.encoder.flush().then(()=>{if(token!==this.epoch)return;this.encoder.close();this.encoder=null;this.chunks.sort((a,b)=>a.timestamp-b.timestamp);this.prepareDecoder(token);}).catch(()=>{if(token===this.epoch)this.abort('unavailable');});}
  }catch(error){this.error=error.message;this.abort('unavailable');}
 }
 prepareDecoder(token){
  this.decoder=new this.api.VideoDecoder({output:frame=>{
   if(token!==this.epoch){frame.close();return;}this.inflight--;this.frames.set(Math.round(frame.timestamp*this.fps/1e6),frame);
   if(this.state==='flushing'&&this.frames.has(0)){this.stateTo('ready');this.onRestore(false);}
  },error:()=>{if(token===this.epoch)this.abort('decode-error');}});
  this.decoder.configure({...this.decoderConfig,codec:this.decoderConfig?.codec||this.config.codec,optimizeForLatency:true});this.pump();
 }
 pump(){while(this.decoder?.state==='configured'&&this.frames.size+this.inflight<4&&this.nextDecode<this.chunks.length){this.inflight++;this.decoder.decode(this.chunks[this.nextDecode++]);}}
 play(){if(this.state!=='ready'||!this.frames.has(0))return false;this.elapsed=0;this.stateTo('playing');return true;}
 present(dt,context){
  if(this.state!=='playing')return null;
  this.elapsed=Math.min(this.seconds,this.elapsed+Math.max(0,dt));const target=Math.floor(this.elapsed*this.fps+1e-6);
  // Drop obsolete surfaces before queuing more; a delayed decode cannot grow memory.
  for(const [i,frame] of this.frames)if(i<target){frame.close();this.frames.delete(i);}
  const frame=this.frames.get(target);
  if(frame){context.drawImage(frame,0,0,this.width,this.height);this.lastPresented=target/this.fps;}
  this.nextDecode=Math.max(this.nextDecode,target);this.pump();
  if(this.elapsed>=this.seconds){this.release();this.stateTo('finished');return this.seconds;}
  return this.elapsed;
 }
 release(){++this.epoch;for(const codec of [this.encoder,this.decoder])try{if(codec&&codec.state!=='closed')codec.close();}catch{}this.encoder=this.decoder=null;for(const frame of this.frames.values())frame.close();this.frames.clear();this.chunks=[];this.bytes=0;this.inflight=0;}
 abort(reason='cancelled'){if(['cancelled','finished','unavailable','memory-limit','decode-error'].includes(this.state))return;const hadWork=this.waiting||this.state==='playing';this.release();this.stateTo(reason);if(hadWork)this.onRestore(true);}
}
