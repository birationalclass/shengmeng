// Small independent arrival surface: no Three.js, models, textures or font requests.
(()=>{
 const canvas=document.getElementById('arrivalSea'),ctx=canvas.getContext('2d',{alpha:false});if(!ctx)return;
 const reduced=matchMedia('(prefers-reduced-motion: reduce)').matches;let frame=0,last=-Infinity;
 function resize(){canvas.width=Math.min(1200,innerWidth);canvas.height=Math.round(canvas.width*innerHeight/innerWidth);paint(0);}
 function paint(t){const w=canvas.width,h=canvas.height,y=h*.4,sunX=w*.57;
 const sky=ctx.createLinearGradient(0,0,0,y);sky.addColorStop(0,'#152b3b');sky.addColorStop(.68,'#79615c');sky.addColorStop(1,'#dd8d62');ctx.fillStyle=sky;ctx.fillRect(0,0,w,y);
 const glow=ctx.createRadialGradient(sunX,y-8,0,sunX,y-8,w*.24);glow.addColorStop(0,'#fbd6a265');glow.addColorStop(1,'#fbd6a200');ctx.fillStyle=glow;ctx.fillRect(0,0,w,y);
 ctx.fillStyle='#f4d29a';ctx.beginPath();ctx.arc(sunX,y,Math.max(9,w*.017),Math.PI,Math.PI*2);ctx.fill();
 const sea=ctx.createLinearGradient(0,y,0,h);sea.addColorStop(0,'#31575c');sea.addColorStop(.35,'#173e45');sea.addColorStop(1,'#072933');ctx.fillStyle=sea;ctx.fillRect(0,y,w,h-y);
 for(let i=0;i<75;i++){const d=(i+1)/75,wy=y+d*d*(h-y),amp=.35+d*2;ctx.beginPath();for(let x=0;x<=w;x+=10){const wave=Math.sin(x*.028+i*2.1+t*.5)*amp+Math.sin(x*.061-i+t*.28)*amp*.3;if(!x)ctx.moveTo(x,wy+wave);else ctx.lineTo(x,wy+wave);}ctx.strokeStyle=`rgba(149,185,175,${.035+d*.12})`;ctx.lineWidth=.4+d*.8;ctx.stroke();
 const rw=(8+d*w*.09)*(1+.35*Math.sin(i*13+t)),rx=sunX+Math.sin(i*21+t*.4)*d*w*.05;ctx.fillStyle=`rgba(242,184,121,${(.35-d*.27)*(0.6+.4*Math.sin(i*5)**2)})`;ctx.fillRect(rx-rw/2,wy,rw,.6+d*1.2);}
 }
 function tick(t){if(!document.body.classList.contains('awaiting-scene')&&!document.body.classList.contains('revealing-scene'))return;if(!document.hidden&&t-last>65){last=t;paint(t/1000);}if(!reduced)frame=requestAnimationFrame(tick);}
 resize();frame=requestAnimationFrame(tick);addEventListener('resize',resize);addEventListener('pagehide',()=>cancelAnimationFrame(frame),{once:true});
})();
