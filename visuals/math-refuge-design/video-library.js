export const VIDEO_LIBRARY_URL='refuge:videos';
export function videoId(value){
 if(/^BV[0-9A-Za-z]{10}$/.test(value))return value;
 try{const u=new URL(value);if(!['https:','http:'].includes(u.protocol)||!['www.bilibili.com','bilibili.com','player.bilibili.com'].includes(u.hostname))return null;const id=u.pathname.match(/^\/video\/(BV[0-9A-Za-z]{10})(?:\/|$)/)?.[1]||u.searchParams.get('bvid');return /^BV[0-9A-Za-z]{10}$/.test(id||'')?id:null;}catch{return null;}
}
export function screenPlayerURL(value){const id=videoId(value);if(!id)return null;const u=new URL('https://player.bilibili.com/player.html');u.searchParams.set('bvid',id);u.searchParams.set('autoplay','1');return u.href;}
export function createVideoLibrary(onNavigate){
 const root=document.createElement('div');root.className='screen-video-library';root.hidden=true;
 root.innerHTML='<div class="video-library-heading"><h2>视频</h2><button type="button" data-original>原版首页 ↗</button></div><form><input aria-label="视频链接或 BV 号" placeholder="粘贴 B 站视频链接或 BV 号"><button type="submit">播放</button></form><p role="status"></p><div class="video-library-grid"></div>';
 const input=root.querySelector('input'),status=root.querySelector('[role=status]'),grid=root.querySelector('.video-library-grid');
 const seed={bvid:'BV1Qrhe6cEaU',title:'OpenAI研究员谈智能体集群与递归式自我改进',author:'DwarkeshPatel'};
 let current=seed.bvid,request=null;
 const saved=new Map([[seed.bvid,seed]]);
 try{for(const v of JSON.parse(localStorage.getItem('refuge-video-links')||'[]'))if(videoId(v.bvid))saved.set(v.bvid,{bvid:v.bvid,title:String(v.title||v.bvid).slice(0,200)});}catch{}
 function remember(id){current=id;if(!saved.has(id))saved.set(id,{bvid:id,title:id});try{localStorage.setItem('refuge-video-links',JSON.stringify([...saved.values()].slice(-30)));}catch{}}
 function play(id){remember(id);onNavigate('https://www.bilibili.com/video/'+id+'/');}
 function render(items){grid.replaceChildren();for(const v of items){const id=videoId(v.bvid);if(!id)continue;const card=document.createElement('button');card.type='button';card.className='video-library-card';
  if(v.cover){try{const u=new URL(v.cover);if(u.protocol==='https:'&&/(^|\.)hdslb\.com$/.test(u.hostname)){const img=document.createElement('img');img.src=u.href;img.loading='lazy';img.referrerPolicy='no-referrer';img.alt='';card.append(img);}}catch{}}
  const title=document.createElement('strong');title.textContent=v.title||id;const author=document.createElement('small');author.textContent=v.author||id;card.append(title,author);card.addEventListener('click',()=>{saved.set(id,{bvid:id,title:v.title||id});play(id);});grid.append(card);
 }}
 root.querySelector('form').addEventListener('submit',e=>{e.preventDefault();const id=videoId(input.value.trim());if(!id){status.textContent='请输入完整 B 站视频链接或 BV 号。';return;}play(id);});
 root.querySelector('[data-original]').addEventListener('click',()=>onNavigate('https://www.bilibili.com/?screen=original'));
 return {root,remember,hide(){root.hidden=true;request?.abort();},async show(){
  request?.abort();request=new AbortController();const own=request;root.hidden=false;render([...saved.values()].reverse());
  // Public cloud endpoint stays unset until a separate deployment is verified.
  const api=['127.0.0.1','localhost'].includes(location.hostname)?'http://127.0.0.1:8783/catalog':null;
  if(!api){status.textContent='已保存的视频 · 可粘贴链接播放；在线推荐尚未启用。';return;}
  status.textContent='正在获取相关推荐…';const timer=setTimeout(()=>own.abort(),12000);
  try{const response=await fetch(api+'?bvid='+encodeURIComponent(current),{signal:own.signal,credentials:'omit'});if(!response.ok)throw new Error();const data=await response.json();if(own!==request||root.hidden)return;render(data.items);status.textContent='当前视频与相关推荐';}
  catch{if(own===request&&!root.hidden)status.textContent='暂时无法获取推荐，以下已保存的视频仍可播放。';}finally{clearTimeout(timer);}
 }};
}
