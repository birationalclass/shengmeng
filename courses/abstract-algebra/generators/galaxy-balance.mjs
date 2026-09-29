export function pointerPose(x,y){const clamp=n=>Math.max(-1,Math.min(1,n));return {x:-clamp(y)*.16,z:-clamp(x)*.18};}
const radians=Math.PI/180;
const wrap=d=>((d+180)%360+360)%360-180;
const response=d=>Math.sign(d)*Math.min(12,Math.max(0,Math.abs(d)-.65)*.4)*radians;
export class BalancePose{
 constructor(){this.reset();}
 reset(){this.base=null;}
 sample(beta,gamma,angle=0){
  if(!Number.isFinite(beta)||!Number.isFinite(gamma))return null;
  if(!this.base||this.base.angle!==angle){this.base={beta,gamma,angle};return {x:0,z:0};}
  const b=wrap(beta-this.base.beta),g=wrap(gamma-this.base.gamma),a=angle*radians;
  return {x:response(b*Math.cos(a)+g*Math.sin(a)),z:-response(g*Math.cos(a)-b*Math.sin(a))};
 }
}
// Permission can be requested by the first mobile entry gesture or explicit enable.
export function createBalanceInput({host=window,onTilt,onState}){
 const pose=new BalancePose();let enabled=false,listening=false,timer=null,state='off';
 const emit=s=>{state=s;onState(s);};
 const clear=()=>{if(timer!==null)host.clearTimeout(timer);timer=null;};
 const center=()=>{pose.reset();onTilt({x:0,z:0});};
 const receive=e=>{
  if(!enabled||host.document.hidden)return;
  const sample=pose.sample(e.beta,e.gamma,host.screen?.orientation?.angle??host.orientation??0);
  if(!sample)return;clear();if(state!=='active')emit('active');onTilt(sample);
 };
 const detach=()=>{if(listening)host.removeEventListener('deviceorientation',receive);listening=false;clear();};
 const attach=()=>{if(!enabled||host.document.hidden)return;center();if(!listening)host.addEventListener('deviceorientation',receive,{passive:true});listening=true;emit('waiting');clear();timer=host.setTimeout(()=>{detach();enabled=false;center();emit('unavailable');},7000);};
 async function enable(){
  if(state==='requesting')return;
  if(!host.isSecureContext){emit('insecure');return;}
  const Device=host.DeviceOrientationEvent;if(!Device){emit('unsupported');return;}
  try{if(typeof Device.requestPermission==='function'){emit('requesting');const result=await Device.requestPermission();if(result!=='granted'){emit('denied');return;}}
   enabled=true;attach();
  }catch{enabled=false;detach();center();emit('denied');}
 }
 function disable(){enabled=false;detach();center();emit('off');}
 const visibility=()=>{detach();center();if(enabled&&!host.document.hidden)attach();};
 const orientation=()=>{center();};
 host.document.addEventListener('visibilitychange',visibility);
 host.screen?.orientation?.addEventListener('change',orientation);
 host.addEventListener('orientationchange',orientation);
 return {enable,disable,recenter:center,get enabled(){return enabled;},get state(){return state;},dispose(){disable();host.document.removeEventListener('visibilitychange',visibility);host.screen?.orientation?.removeEventListener('change',orientation);host.removeEventListener('orientationchange',orientation);}};
}
export function mountBalanceControls(world){
 if(!world)return;
 const mobile=matchMedia('(pointer:coarse)').matches||navigator.maxTouchPoints>0;
 const tools=document.querySelector('.cosmic-tools');
 const quick=document.createElement('button');quick.id='cosmicBalance';quick.className='balance-quick';quick.hidden=!mobile;
 quick.innerHTML='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.4" aria-hidden="true"><rect x="7" y="2" width="10" height="20" rx="2" transform="rotate(15 12 12)"/><path d="M2 10a10 10 0 0 0 2 7m18-3a10 10 0 0 0-2-7"/></svg>';tools.prepend(quick);
 const section=document.createElement('section');section.className='balance-settings';section.innerHTML='<button id="balanceToggle"></button><button id="balanceCenter"></button><p id="balanceStatus" role="status"></p>';document.querySelector('#cosmicPreferences').append(section);
 const toggle=section.querySelector('#balanceToggle'),center=section.querySelector('#balanceCenter'),status=section.querySelector('#balanceStatus');
 let state='off';
 const input=createBalanceInput({onTilt:value=>{world.mouseView=false;world.balanceTarget.set(value.x,value.z);},onState:value=>{state=value;sync();}});
 function sync(){const en=document.documentElement.lang==='en',t=(zh,eng)=>en?eng:zh;
  const label=input.enabled?t('关闭重力控制','Disable tilt control'):t('开启重力控制','Enable tilt control');
  quick.title=label;quick.dataset.tip=label;quick.setAttribute('aria-label',label);quick.setAttribute('aria-pressed',String(state==='active'));quick.disabled=state==='requesting';
  toggle.textContent=label;toggle.disabled=state==='requesting';center.textContent=t('以当前姿势居中','Recenter at current position');center.disabled=!input.enabled;
  const messages={off:['倾斜手机，轻转星群','Tilt your phone to turn the galaxy'],requesting:['请允许设备方向访问','Allow orientation access'],waiting:['保持舒适姿势，等待传感器','Hold comfortably; waiting for sensor'],active:['重力控制已开启','Tilt control enabled'],denied:['未获授权，可再次点击开启','Permission not granted; tap to retry'],unsupported:['此浏览器不支持重力控制','Orientation is not supported here'],unavailable:['未收到姿态数据，可重试','No orientation data; tap to retry'],insecure:['请使用 HTTPS 在线页面开启','Open the HTTPS website to enable']};status.textContent=t(...messages[state]);
 }
 let autoPending=mobile;const toggleInput=()=>{autoPending=false;return input.enabled?input.disable():input.enable();};quick.onclick=toggleInput;toggle.onclick=toggleInput;center.onclick=()=>input.recenter();
 window.addEventListener('cosmic-ui-change',sync);sync();
 if(mobile&&window.isSecureContext&&window.DeviceOrientationEvent){if(typeof DeviceOrientationEvent.requestPermission!=='function'){autoPending=false;void input.enable();}else{const firstGesture=e=>{if(!autoPending)return;if(e.target.closest?.('#cosmicBalance,#balanceToggle'))return;autoPending=false;document.removeEventListener('click',firstGesture);void input.enable();};document.addEventListener('click',firstGesture);}}
 return input;
}
