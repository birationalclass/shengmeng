// Conservative screen-space LOD. The small corner tessellation changes only
// once an entire object occupies a few pixels; no level ever removes a mesh.
export function roundedDetailLevel(pixelRadius,previous=0){
  return previous===1?(pixelRadius>8?0:1):(pixelRadius<6?1:0);
}

// Actual GPU time, not requestAnimationFrame frequency: an inactive browser tab
// or a 30 Hz display must not be mistaken for a GPU bottleneck.
export class RenderBudget{
  constructor(){this.reset();}
  reset(){this.scale=1;this.samples=[];this.changedAt=0;this.lastSampleAt=0;this.gpuMs=null;this.reading=false;}
  sample(ms,now){
    if(!Number.isFinite(ms)||ms<=0||ms>150)return;
    if(now-this.lastSampleAt>1500)this.samples=[];
    this.lastSampleAt=now;this.samples.push(ms);if(this.samples.length>12)this.samples.shift();
  }
  update(now,{enabled=true,reading=false,mobile=false}={}){
    const floor=reading?(mobile?.96:.80):(mobile?.76:.65);
    if(!enabled){this.reset();return this.scale;}
    if(reading!==this.reading){this.reading=reading;this.samples=[];}
    if(this.scale<floor){this.scale=floor;this.changedAt=now;this.samples=[];return this.scale;}
    if(this.samples.length<8||now-this.lastSampleAt>1500||now-this.changedAt<2000)return this.scale;
    const ordered=[...this.samples].sort((a,b)=>a-b);
    this.gpuMs=ordered[Math.floor(ordered.length*.75)];
    let next=this.scale;
    if(this.gpuMs>19)next=Math.max(floor,this.scale-Math.min(.12,Math.max(.04,this.scale*(1-Math.sqrt(16/this.gpuMs)))));
    else if(this.gpuMs<12&&now-this.changedAt>=6000)next=Math.min(1,this.scale+.02);
    next=Number(next.toFixed(2));
    if(next!==this.scale){this.scale=next;this.changedAt=now;this.samples=[];}
    return this.scale;
  }
}

// Poll only completed queries. Never gl.finish(), wait on a result, or retain
// an unbounded query queue. Unsupported browsers keep the selected quality.
export function createGpuTimer(gl){
  const ext=gl.getExtension?.('EXT_disjoint_timer_query_webgl2');
  const supported=Boolean(ext&&gl.createQuery&&gl.getQuery(ext.TIME_ELAPSED_EXT,ext.QUERY_COUNTER_BITS_EXT)>0);
  let pending=null,active=false,started=0;
  const clear=()=>{if(pending)gl.deleteQuery(pending);pending=null;};
  return {supported,
    begin(now){
      if(!supported||pending||now-started<200||gl.isContextLost())return;
      if(gl.getQuery(ext.TIME_ELAPSED_EXT,gl.CURRENT_QUERY))return;
      pending=gl.createQuery();if(!pending)return;
      started=now;gl.beginQuery(ext.TIME_ELAPSED_EXT,pending);active=true;
    },
    end(){if(active){gl.endQuery(ext.TIME_ELAPSED_EXT);active=false;}},
    poll(now){
      if(!pending||active)return null;
      if(gl.isContextLost()||gl.getParameter(ext.GPU_DISJOINT_EXT)||now-started>1500){clear();return null;}
      if(!gl.getQueryParameter(pending,gl.QUERY_RESULT_AVAILABLE))return null;
      const ms=gl.getQueryParameter(pending,gl.QUERY_RESULT)/1e6;clear();return ms;
    },
    dispose(){if(active)this.end();clear();}
  };
}
