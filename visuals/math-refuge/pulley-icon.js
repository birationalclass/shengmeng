// One compact pulley symbol shared by the wall control and speaker console.
export function drawPulley(ctx,x,y,size,progress=0,stored=false){
 ctx.save();ctx.translate(x,y);const s=size/100;ctx.scale(s,s);
 ctx.fillStyle='#c4d6ce';ctx.fillRect(-30,-43,60,3);ctx.fillRect(-2,-43,4,10);
 ctx.fillStyle='#e7c78f';ctx.beginPath();ctx.arc(0,-16,18,0,Math.PI*2);ctx.fill();
 ctx.fillStyle='#203b37';ctx.beginPath();ctx.arc(0,-16,14,0,Math.PI*2);ctx.fill();
 ctx.save();ctx.translate(0,-16);ctx.rotate(progress*Math.PI*3);ctx.fillStyle='#e7c78f';
 for(let i=0;i<3;i++){ctx.rotate(Math.PI*2/3);ctx.fillRect(-1.5,-12,3,12);}ctx.beginPath();ctx.arc(0,0,4,0,Math.PI*2);ctx.fill();ctx.restore();
 const drop=progress*10;ctx.fillStyle='#c4d6ce';ctx.fillRect(-19,-16,2,40+drop);ctx.fillRect(17,-16,2,48-drop);
 ctx.fillStyle='#e7c78f';ctx.fillRect(-30,23+drop,26,19);ctx.fillStyle='#203b37';ctx.fillRect(-27,26+drop,20,13);
 ctx.fillStyle='#e7c78f';ctx.fillRect(14,30-drop,8,5);
 ctx.beginPath();const ay=stored?6:18;ctx.moveTo(28,ay);ctx.lineTo(35,ay+(stored?-8:8));ctx.lineTo(42,ay);ctx.lineTo(38,ay);ctx.lineTo(38,ay+(stored?13:-13));ctx.lineTo(32,ay+(stored?13:-13));ctx.lineTo(32,ay);ctx.fill();
 ctx.restore();
}
