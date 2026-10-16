// Explicit verification URL only. Never writes user volume or playback settings.
if(typeof location!=='undefined'&&new URL(location.href).searchParams.has('testSilent')){
 const play=HTMLMediaElement.prototype.play;
 HTMLMediaElement.prototype.play=function(...args){this.muted=true;this.volume=0;return play.apply(this,args);};
 if(typeof AudioNode!=='undefined'){const connect=AudioNode.prototype.connect,sinks=new WeakMap();AudioNode.prototype.connect=function(target,...args){if(typeof AudioDestinationNode!=='undefined'&&target instanceof AudioDestinationNode){let sink=sinks.get(target);if(!sink){sink=this.context.createGain();sink.gain.value=0;connect.call(sink,target);sinks.set(target,sink);}return connect.call(this,sink,...args);}return connect.call(this,target,...args);};}
 document.documentElement.dataset.testSilent='true';
}
