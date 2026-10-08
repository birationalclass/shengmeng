import {loadPart} from './crypto.js?v=20261009-stream2';
export class SegmentedVideo {
  constructor(video,asset,key,signal,onStatus=()=>{}) {
    Object.assign(this,{video,asset,key,signal,onStatus});this.loaded=new Set();this.destroyed=false;this.busy=false;this.again=false;
    const types=[globalThis.MediaSource,globalThis.ManagedMediaSource].filter(Boolean);
    this.Type=types.find(T=>T.isTypeSupported(asset.mime));
    if(!this.Type)throw new Error('当前浏览器不支持此视频播放，请使用新版 Safari、Chrome 或 Edge。');
    this.media=new this.Type();video.disableRemotePlayback=true;video.controls=false;
    this.url=URL.createObjectURL(this.media);video.src=this.url;
    this.schedule=()=>this.pump().catch(e=>{if(e.name!=='AbortError'&&!this.destroyed)this.onStatus(e.message,true);});
    for(const event of ['play','timeupdate','waiting','seeking'])video.addEventListener(event,this.schedule);
    this.abort=()=>this.destroy();signal?.addEventListener('abort',this.abort,{once:true});
  }
  async open() {
    await new Promise((resolve,reject)=>{
      const timer=setTimeout(()=>done(new Error('播放器初始化超时，请重试。')),15000);
      const done=error=>{clearTimeout(timer);this.media.removeEventListener('sourceopen',ready);this.signal?.removeEventListener('abort',cancel);error?reject(error):resolve();};
      const ready=()=>done();const cancel=()=>done(new DOMException('Aborted','AbortError'));
      this.media.addEventListener('sourceopen',ready,{once:true});this.signal?.addEventListener('abort',cancel,{once:true});
      if(this.media.readyState==='open')done();
    });
    this.sb=this.media.addSourceBuffer(this.asset.mime);this.media.duration=this.asset.duration;
    await this.append(await loadPart(this.asset,0,this.key,this.signal));
    await this.fragment(0);this.onStatus('');return this;
  }
  async change(fn) {
    if(this.destroyed||this.signal?.aborted)throw new DOMException('Aborted','AbortError');
    await new Promise((resolve,reject)=>{
      const clean=()=>{this.sb.removeEventListener('updateend',end);this.sb.removeEventListener('error',error);this.signal?.removeEventListener('abort',abort);};
      const end=()=>{clean();resolve();};const error=()=>{clean();reject(new Error('视频片段无法播放，请重试。'));};const abort=()=>{clean();reject(new DOMException('Aborted','AbortError'));};
      this.sb.addEventListener('updateend',end,{once:true});this.sb.addEventListener('error',error,{once:true});this.signal?.addEventListener('abort',abort,{once:true});
      try{fn();}catch(e){clean();reject(e);}
    });
  }
  append(data){return this.change(()=>this.sb.appendBuffer(data));}
  async fragment(index) {
    if(this.loaded.has(index))return;
    const data=await loadPart(this.asset,index+1,this.key,this.signal);
    await this.append(data);this.loaded.add(index);this.video.dataset.loadedSegments=String(this.loaded.size);
  }
  async prune(time) {
    const before=Math.max(0,time-16),after=Math.min(this.asset.duration,time+24);
    if(before>0){await this.change(()=>this.sb.remove(0,before));for(const i of this.loaded)if(this.asset.segments[i].start<before)this.loaded.delete(i);}
    if(after<this.asset.duration&&this.sb.buffered.length&&this.sb.buffered.end(this.sb.buffered.length-1)>after){await this.change(()=>this.sb.remove(after,this.asset.duration+.1));for(const i of this.loaded)if(this.asset.segments[i].start+this.asset.segments[i].duration>after)this.loaded.delete(i);}
  }
  async pump() {
    if(!this.sb||this.destroyed||this.signal?.aborted)return;
    if(this.busy){this.again=true;return;}this.busy=true;
    try {
      const time=this.video.currentTime;const paused=this.video.paused;
      let target=this.asset.segments.findIndex(s=>time>=s.start-.04&&time<s.start+s.duration-.04);
      if(target<0)target=this.asset.segments.length-1;
      if(paused&&!this.video.seeking&&this.loaded.has(target))return;
      await this.prune(time);
      const end=paused?target+1:Math.min(this.asset.segments.length,target+3);
      for(let i=target;i<end;i++) {
        if(this.destroyed||Math.abs(this.video.currentTime-time)>12)break;
        await this.fragment(i);
        if(this.video.paused)break;
      }
      if(this.loaded.has(this.asset.segments.length-1)&&this.media.readyState==='open'&&!this.sb.updating)this.media.endOfStream();
    } finally {this.busy=false;if(this.again&&!this.destroyed){this.again=false;queueMicrotask(this.schedule);}}
  }
  destroy() {
    if(this.destroyed)return;this.destroyed=true;
    for(const event of ['play','timeupdate','waiting','seeking'])this.video.removeEventListener(event,this.schedule);
    this.signal?.removeEventListener('abort',this.abort);
    this.video.pause();this.video.removeAttribute('src');this.video.load();URL.revokeObjectURL(this.url);
  }
}
export function playerControls(video,root) {
  const toggle=root.querySelector('[data-toggle]'),seek=root.querySelector('[data-seek]'),time=root.querySelector('[data-time]'),volume=root.querySelector('[data-volume]'),full=root.querySelector('[data-fullscreen]');
  const wrapper=root.parentElement;let hideTimer;
  wrapper.tabIndex=0;wrapper.setAttribute('aria-label',video.getAttribute('aria-label')||'视频播放器');
  const show=()=>{clearTimeout(hideTimer);wrapper.classList.remove('controls-hidden');root.removeAttribute('aria-hidden');root.inert=false;};
  const hide=()=>{if(video.paused||video.seeking||root.hidden||wrapper.querySelector(':focus-visible'))return;wrapper.classList.add('controls-hidden');root.setAttribute('aria-hidden','true');root.inert=true;};
  const activity=()=>{show();if(!video.paused)hideTimer=setTimeout(hide,2800);};
  for(const event of ['pointermove','pointerdown','focusin'])wrapper.addEventListener(event,activity);
  wrapper.addEventListener('pointerleave',()=>{clearTimeout(hideTimer);if(!video.paused)hideTimer=setTimeout(hide,1000);});
  wrapper.addEventListener('focusout',activity);
  wrapper.addEventListener('keydown',event=>{
    activity();if(event.target!==wrapper)return;
    if(event.key===' '){event.preventDefault();video.paused?video.play().catch(()=>{}):video.pause();}
    if(event.key==='ArrowLeft'||event.key==='ArrowRight'){event.preventDefault();video.currentTime=Math.max(0,Math.min(video.duration||0,video.currentTime+(event.key==='ArrowLeft'?-5:5)));}
  });
  for(const event of ['play','playing','seeked'])video.addEventListener(event,activity);
  for(const event of ['pause','ended','emptied'])video.addEventListener(event,show);
  const stamp=n=>`${Math.floor(n/60)}:${String(Math.floor(n%60)).padStart(2,'0')}`;
  const update=()=>{const duration=Number.isFinite(video.duration)?video.duration:Number(seek.max);if(duration>0)seek.max=String(duration);seek.value=String(video.currentTime);toggle.textContent=video.paused?'▶':'Ⅱ';toggle.setAttribute('aria-label',video.paused?'播放':'暂停');time.textContent=`${stamp(video.currentTime)} / ${stamp(duration||0)}`;};
  toggle.addEventListener('click',()=>video.paused?video.play().catch(()=>{}):video.pause());
  seek.addEventListener('input',()=>{video.currentTime=Number(seek.value);update();});
  volume.addEventListener('input',()=>{video.volume=Number(volume.value);});
  full.addEventListener('click',()=>{if(document.fullscreenElement)document.exitFullscreen();else if(wrapper.requestFullscreen)wrapper.requestFullscreen();else video.webkitEnterFullscreen?.();});
  for(const event of ['play','pause','timeupdate','loadedmetadata','durationchange','ended'])video.addEventListener(event,update);
  video.addEventListener('contextmenu',event=>event.preventDefault());update();return update;
}
