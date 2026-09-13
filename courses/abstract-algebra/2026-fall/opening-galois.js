/* Original sand engravings for the life and afterlife of Galois's ideas. */
(() => {
  'use strict';
  const countParts=[.68,.25,.07];
  const nodes=Object.freeze([
    {id:'portrait',year:'1811–1832',motif:'portrait'},
    {id:'awakening',year:'1827',motif:'open book, compass and geometry'},
    {id:'symmetries',year:'1830–1831',motif:'five roots and their permutations'},
    {id:'prison',year:'1831–1832',motif:'the young Galois writing beneath a barred window'},
    {id:'letter',year:'29 May 1832',motif:'a letter, quill and candle'},
    {id:'last-dawn',year:'30–31 May 1832',motif:'two distant figures at dawn'},
    {id:'echoes',year:'1832–1846',motif:'a silent parchment manuscript and falling autumn leaves'}
  ].map(Object.freeze));
  function rng(initial){let seed=initial>>>0;return()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};}

  // Thin the actual serif letterforms, rather than draw hollow outlines. The
  // medial line retains each glyph; its local radius is one third of the ink.
  function thinLettering(alpha,width,height){
    const n=width*height,mask=new Uint8Array(n),distance=new Float32Array(n);
    for(let i=0;i<n;i++){mask[i]=alpha[i*4+3]>150?1:0;distance[i]=mask[i]?1e4:0;}
    const d=Math.SQRT2;
    for(let y=1;y<height-1;y++)for(let x=1;x<width-1;x++){const i=y*width+x;if(mask[i])distance[i]=Math.min(distance[i],distance[i-1]+1,distance[i-width]+1,distance[i-width-1]+d,distance[i-width+1]+d);}
    for(let y=height-2;y>0;y--)for(let x=width-2;x>0;x--){const i=y*width+x;if(mask[i])distance[i]=Math.min(distance[i],distance[i+1]+1,distance[i+width]+1,distance[i+width+1]+d,distance[i+width-1]+d);}
    const removals=[];
    for(let pass=0;pass<80;pass++){
      let changed=0;
      for(let step=0;step<2;step++){
        removals.length=0;
        for(let y=1;y<height-1;y++)for(let x=1;x<width-1;x++){
          const i=y*width+x;if(!mask[i])continue;
          const p=[mask[i-width],mask[i-width+1],mask[i+1],mask[i+width+1],mask[i+width],mask[i+width-1],mask[i-1],mask[i-width-1]];
          const sum=p.reduce((a,b)=>a+b,0);if(sum<2||sum>6)continue;
          let edges=0;for(let j=0;j<8;j++)if(!p[j]&&p[(j+1)%8])edges++;
          if(edges!==1)continue;
          if(step===0?(p[0]*p[2]*p[4]||p[2]*p[4]*p[6]):(p[0]*p[2]*p[6]||p[0]*p[4]*p[6]))continue;
          removals.push(i);
        }
        for(const i of removals)mask[i]=0;changed+=removals.length;
      }
      if(!changed)break;
    }
    const fine=new Uint8Array(n);
    for(let i=0;i<n;i++)if(mask[i]){
      const x=i%width,y=(i/width)|0,r=Math.max(.58,(distance[i]-.5)/3),edge=Math.ceil(r);
      for(let dy=-edge;dy<=edge;dy++)for(let dx=-edge;dx<=edge;dx++)if(dx*dx+dy*dy<=r*r){const j=(y+dy)*width+x+dx;if(j>=0&&j<n)fine[j]=1;}
      fine[i]=1;
    }
    const ink=[];for(let y=0;y<height;y++)for(let x=0;x<width;x++)if(fine[y*width+x])ink.push([x,y]);return ink;
  }
  const letteringCache=new Map();
  function textPixels(text,font,tracking){
    const key=text+font+tracking;if(letteringCache.has(key))return letteringCache.get(key);
    const c=document.createElement('canvas');c.width=1600;c.height=260;
    const ctx=c.getContext('2d',{willReadFrequently:true});ctx.fillStyle='#fff';ctx.textAlign='left';ctx.textBaseline='middle';ctx.font=font;
    const widths=[...text].map(ch=>ctx.measureText(ch).width),total=widths.reduce((a,b)=>a+b,0)+tracking*(widths.length-1);
    let x=800-total/2;[...text].forEach((ch,i)=>{ctx.fillText(ch,x,130);x+=widths[i]+tracking;});
    const ink=thinLettering(ctx.getImageData(0,0,1600,260).data,1600,260);
    if(!ink.length)throw new Error('Galois lettering could not be prepared');letteringCache.set(key,ink);return ink;
  }
  function pack(points,count,componentCounts){
    for(const p of points){p[3]=Math.atan2(p[1],p[0]);p[4]=p[0]*p[0]+p[1]*p[1];}
    points.sort((a,b)=>a[3]-b[3]||a[4]-b[4]);
    const positions=new Float32Array(count*3),normals=new Float32Array(count*3),flat=new Float32Array(count*2);
    points.forEach((p,i)=>{positions[i*3]=p[0];positions[i*3+1]=p[1];positions[i*3+2]=p[2];normals[i*3+2]=1;flat[i*2]=p[0];flat[i*2+1]=p[1];});
    return {positions,normals,flat,componentCounts};
  }
  function sample(count){
    const binary=atob(window.CourseOpeningGaloisPortrait),bytes=Uint8Array.from(binary,c=>c.charCodeAt(0)),view=new DataView(bytes.buffer),portraitCount=bytes.length/4;
    const title=textPixels('Évariste Galois','400 160px Georgia, "Times New Roman", serif',-3.2);
    const dates=textPixels('1811–1832','400 100px Georgia, "Times New Roman", serif',-2.2);
    const random=rng(18111832),points=[],componentCounts=[0,0,0];
    for(let i=0;i<count;i++){
      let x,y,id;
      if(i<count*countParts[0]){
        id=0;const j=Math.floor(random()*portraitCount)*4;
        x=(view.getUint16(j,true)/65535-.5)*.94+(random()-.5)*.0012;
        y=.88-view.getUint16(j+2,true)/65535*1.28+(random()-.5)*.0012;
      }else{
        id=i<count*(countParts[0]+countParts[1])?1:2;
        const ink=id===1?title:dates,p=ink[Math.floor(random()*ink.length)],scale=id===1?740:930;
        x=(p[0]+random()-800)/scale;y=(130-p[1]-random())/scale+(id===1?-.525:-.735);
      }
      points.push([x,y,(random()-.5)*.003]);componentCounts[id]++;
    }
    return pack(points,count,componentCounts);
  }

  // World-coordinate engraving helpers. Translucent fills give the sand a
  // quiet body; narrow contours and spaced hatching carry the readable shape.
  function drawing(){
    const size=1400,scale=size/2,c=document.createElement('canvas');c.width=c.height=size;
    const ctx=c.getContext('2d',{willReadFrequently:true});ctx.setTransform(scale,0,0,-scale,size/2,size/2);ctx.lineCap='round';ctx.lineJoin='round';
    const style=(width=.003,alpha=1)=>{ctx.lineWidth=width;ctx.strokeStyle=`rgba(255,255,255,${alpha})`;ctx.fillStyle=`rgba(255,255,255,${alpha})`;};
    const line=(points,width=.003,alpha=1,close=false,fill=false)=>{style(width,alpha);ctx.beginPath();ctx.moveTo(...points[0]);for(const p of points.slice(1))ctx.lineTo(...p);if(close)ctx.closePath();fill?ctx.fill():ctx.stroke();};
    const curve=(start,controls,width=.003,alpha=1)=>{style(width,alpha);ctx.beginPath();ctx.moveTo(...start);for(const p of controls)p.length===6?ctx.bezierCurveTo(...p):ctx.quadraticCurveTo(...p);ctx.stroke();};
    const ellipse=(x,y,rx,ry,width=.003,alpha=1,fill=false,rotation=0)=>{style(width,alpha);ctx.beginPath();ctx.ellipse(x,y,rx,ry,rotation,0,Math.PI*2);fill?ctx.fill():ctx.stroke();};
    const dot=(x,y,r=.005,alpha=1)=>ellipse(x,y,r,r,.001,alpha,true);
    return{c,ctx,size,scale,style,line,curve,ellipse,dot};
  }
  function openBook(d,cy=-.22,s=.95){
    const{line,curve}=d;
    const t=p=>[p[0]*s,p[1]*s+cy];
    const left=[[-.76,.18],[-.44,.24],[-.05,.1],[0,-.52],[-.4,-.36],[-.8,-.4]];
    const right=[[0,-.52],[.05,.1],[.41,.24],[.75,.14],[.81,-.4],[.41,-.37]];
    line(left.map(t),.002,.075,true,true);line(right.map(t),.002,.07,true,true);
    line(left.map(t),.006,.92,true);line(right.map(t),.006,.92,true);
    curve(t([0,-.52]),[[.012*s,-.08*s+cy,-.015*s,.02*s+cy,0,.13*s+cy]],.005,.9);
    for(let k=0;k<4;k++){
      const f=k*.012;
      curve(t([-.8,-.41-f]),[[-.43*s,(-.36-f)*s+cy,-.13*s,(-.48-f)*s+cy,0,(-.55-f)*s+cy]],.002,.6);
      curve(t([0,-.55-f]),[[.25*s,(-.45-f)*s+cy,.59*s,(-.43-f)*s+cy,.81*s,(-.41-f)*s+cy]],.002,.6);
    }
    for(let j=0;j<14;j++){
      const y=.11-j*.031;
      curve(t([-.68,y]),[[-.49*s,(y+.028)*s+cy,-.3*s,(y-.038)*s+cy,-.105*s,(y-.074)*s+cy]],.0017,j%4===0?.75:.43);
      curve(t([.11,y-.075]),[[.29*s,(y-.027)*s+cy,.53*s,(y+.024)*s+cy,.66*s,(y-.012)*s+cy]],.0017,j%4===0?.75:.43);
    }
  }
  function awakening(d){
    const{line,curve,ellipse,dot}=d;openBook(d,-.05,.93);
    // A compass above an open book, with a circle and its constructed triangle.
    ellipse(-.31,.50,.22,.22,.0035,.9);line([[-.50,.39],[-.11,.39],[-.31,.71],[-.50,.39]],.004,.92);
    line([[-.31,.26],[-.31,.75]],.0018,.4);line([[-.56,.50],[-.065,.50]],.0018,.4);
    [-.31,-.50,-.11].forEach((x,i)=>dot(x,i===0?.71:.39,.009));
    const pivot=[.34,.70];ellipse(...pivot,.022,.025,.005,1);line([[.32,.68],[.13,.15],[.16,.18],[.35,.64]],.008,.94);line([[.355,.68],[.56,.14],[.53,.16],[.33,.64]],.009,.94);
    line([[.23,.40],[.45,.40]],.004,.8);ellipse(.34,.40,.007,.012,.002,1,true);
    curve([.08,.17],[[.22,.04,.44,.025,.61,.17]],.0027,.6);
    for(let j=0;j<9;j++){const x=.235+j*.018;line([[x,.66-(x-.235)*1.7],[x+.035,.61-(x-.235)*1.7]],.0014,.38);}
  }
  function symmetries(d){
    const{line,curve,ellipse,dot}=d;
    const roots=Array.from({length:5},(_,i)=>{const a=Math.PI/2+i*2*Math.PI/5;return[.55*Math.cos(a),.04+.55*Math.sin(a)];});
    ellipse(0,.04,.63,.63,.0025,.38);ellipse(0,.04,.665,.665,.0017,.25);
    // Two interleaving cycles connect the same five roots: permutations become visible.
    for(let i=0;i<5;i++){
      const a=roots[i],b=roots[(i+1)%5],c=roots[(i+2)%5];
      curve(a,[[a[0]*.82,a[1]*.82,b[0]*.82,b[1]*.82,...b]],.005,.9);
      curve(a,[[a[0]*.23,a[1]*.23+.04,c[0]*.23,c[1]*.23+.04,...c]],.0028,.65);
      ellipse(...a,.057,.057,.005,1);ellipse(...a,.040,.040,.0024,.6);dot(...a,.012,.9);
      // Arrowheads belong to the outer cycle, keeping the visual mathematical.
      const mx=a[0]*.27+b[0]*.73,my=a[1]*.27+b[1]*.73,dx=b[0]-a[0],dy=b[1]-a[1],len=Math.hypot(dx,dy),ux=dx/len,uy=dy/len;
      line([[mx-ux*.039-uy*.023,my-uy*.039+ux*.023],[mx,my],[mx-ux*.039+uy*.023,my-uy*.039-ux*.023]],.0035,.94);
    }
    for(let j=0;j<40;j++){const a=j*Math.PI/20,r=.70+(j%5===0?.03:0);line([[.686*Math.cos(a),.04+.686*Math.sin(a)],[r*Math.cos(a),.04+r*Math.sin(a)]],.0018,.48);}
    // A small radical is a question that the symmetry diagram answers.
    line([[-.16,-.78],[-.13,-.745],[-.07,-.825],[0,-.67],[.23,-.67]],.006,.85);
    curve([.07,-.71],[[.12,-.70,.15,-.79,.20,-.78]],.0027,.9);
    curve([.19,-.71],[[.16,-.73,.11,-.77,.075,-.78]],.0027,.9);
  }
  function prison(d){
    const{line,curve,ellipse}=d;
    // The cell surrounds a substantial young figure, instead of replacing him
    // with a prison symbol. His face uses the same historical portrait grains.
    const arch=()=>{d.ctx.beginPath();d.ctx.moveTo(.04,-.20);d.ctx.lineTo(.04,.37);d.ctx.ellipse(.39,.37,.35,.39,0,Math.PI,0,true);d.ctx.lineTo(.74,-.20);d.ctx.closePath();};
    d.style(.0065,.74);arch();d.ctx.stroke();d.style(.003,.022);arch();d.ctx.fill();
    curve([0,-.22],[[0,.04,0,.20,0,.38],[0,.94,.78,.94,.78,.38],[.78,.18,.78,0,.78,-.22]],.0025,.42);
    for(const x of[.16,.28,.40,.52,.64]){const top=.37+.39*Math.sqrt(Math.max(0,1-((x-.39)/.35)**2));line([[x,-.19],[x,top]],.007,.79);line([[x+.006,-.19],[x+.006,top-.01]],.0014,.3);}
    for(const y of[.02,.29,.51])line([[.05,y],[.73,y]],.0048,.65);
    line([[0,-.21],[.77,-.21],[.81,-.255],[-.03,-.255],[0,-.21]],.0037,.71);
    for(let j=0;j<6;j++){const x=.11+j*.103;line([[x,-.26],[x-.11,-.45]],.0016,.24);}
    for(let j=0;j<7;j++){const y=-.14+j*.128;line([[-.82,y],[-.66,y+.004]],.0018,.18);line([[.80,y],[.88,y-.004]],.0018,.18);}
    // Collar, coat, writing arm and the edge of a narrow desk.
    const coat=[[-.47,.21],[-.61,.12],[-.69,-.06],[-.67,-.50],[-.46,-.62],[-.23,-.52],[-.12,-.30],[-.18,.04],[-.31,.17]];
    line(coat,.002,.11,true,true);line(coat,.005,.9,true);
    curve([-.60,.09],[[-.54,-.10,-.54,-.30,-.62,-.48]],.0025,.63);
    curve([-.41,.12],[[-.29,-.06,-.32,-.31,-.26,-.51]],.0027,.68);
    line([[-.43,.19],[-.31,-.02],[-.22,.16]],.0042,.92);
    line([[-.40,.16],[-.35,-.10],[-.29,-.015]],.0023,.65);
    for(let j=0;j<13;j++){const x=-.65+j*.025;curve([x,-.43],[[x+.065,-.25,x+.035,-.10,x+.072,.04-j*.007]],.0012,.31);}
    // The known curls, forehead, nose and young face of Galois, cropped from
    // Alfred Galois's portrait rather than invented as a generic silhouette.
    const binary=atob(window.CourseOpeningGaloisPortrait),bytes=Uint8Array.from(binary,c=>c.charCodeAt(0)),view=new DataView(bytes.buffer);
    d.ctx.fillStyle='rgba(255,255,255,.88)';
    for(let j=0;j<bytes.length;j+=4){const u=view.getUint16(j,true)/65535,v=view.getUint16(j+2,true)/65535;if(v>.55||u<.23||u>.84)continue;d.ctx.fillRect(-.45+(u-.50)*.84,.73-v*1.055,.0019,.0019);}
    const sleeve=[[-.32,.035],[-.21,-.04],[-.18,-.20],[.035,-.285],[.008,-.335],[-.32,-.285],[-.44,-.105]];
    line(sleeve,.002,.10,true,true);line(sleeve,.0045,.88,true);
    curve([-.37,-.10],[[-.27,-.19,-.28,-.24,-.07,-.30]],.002,.56);
    curve([.013,-.286],[[.063,-.26,.09,-.271,.119,-.293],[.14,-.319,.091,-.324,.044,-.324]],.0036,.89);
    for(let j=0;j<3;j++)line([[.055+j*.018,-.279],[.075+j*.018,-.311]],.0016,.61);
    line([[-.72,-.51],[.54,-.36],[.80,-.49],[-.43,-.70],[-.72,-.51]],.004,.79);
    line([[-.44,-.71],[-.45,-.84]],.005,.7);line([[.70,-.51],[.70,-.81]],.005,.65);
    const paper=[[-.03,-.35],[.43,-.305],[.63,-.472],[.15,-.55]];line(paper,.002,.049,true,true);line(paper,.0039,.9,true);
    for(let j=0;j<7;j++){const y=-.374-j*.021;curve([.075+j*.008,y],[[.20,y+.013,.34,y+.004,.46-j*.003,y-.010]],.0017,.64);}
    line([[.115,-.291],[.253,-.41]],.003,.95);
    curve([.114,-.290],[[.058,-.19,.036,-.079,.035,-.02],[.12,-.072,.156,-.192,.114,-.290]],.0024,.66);
    for(let j=0;j<7;j++){const y=-.26+j*.027;line([[.11,y],[.065,y+.041]],.0011,.5);}
    ellipse(.57,-.316,.045,.014,.0025,.64);line([[.528,-.315],[.532,-.362],[.61,-.37],[.61,-.315]],.0026,.63);
  }
  function letter(d){
    const{line,curve,ellipse,dot}=d;
    const paper=[[-.72,-.24],[.29,-.16],[.57,-.72],[-.56,-.81]];line(paper,.002,.075,true,true);line(paper,.005,.97,true);
    line([[-.56,-.82],[.57,-.73],[.58,-.70]],.002,.64);
    for(let j=0;j<12;j++){
      const y=-.31-j*.029,start=-.58+j*.010,end=.20+j*.013;
      curve([start,y],[[start+.15,y+.018,end-.19,y-.008,end,y+.015]],.0022,j<3?.83:.56);
      if(j%3===0)curve([end+.03,y+.008],[[end+.07,y+.034,end+.11,y-.014,end+.14,y+.012]],.0018,.55);
    }
    // The feather's shaft points exactly at the writing, not at decorative air.
    curve([.08,-.36],[[.25,-.07,.38,.27,.59,.74]],.006,.95);
    curve([.25,-.04],[[.21,.18,.33,.59,.60,.76],[.76,.43,.57,.09,.25,-.04]],.0035,.92);
    for(let j=0;j<28;j++){
      const u=j/28,x=.27+.31*u,y=.015+.71*u;
      curve([x,y],[[x-.055*(1-u),y+.012,x-.15*(1-u),y+.095,x-.085*(1-u),y+.14]],.0018,.56);
      curve([x,y],[[x+.05*(1-u),y+.015,x+.15*(1-u),y+.075,x+.12*(1-u),y+.14]],.0018,.65);
    }
    ellipse(.55,-.19,.095,.029,.004,.9);line([[.465,-.19],[.45,-.32],[.61,-.33],[.64,-.19]],.005,.86);ellipse(.544,-.329,.085,.021,.003,.6);ellipse(.55,-.19,.058,.014,.003,.7);
    // A solitary candle, its halo engraved as a sparse family of arcs.
    line([[-.54,.48],[-.55,-.13],[-.34,-.13],[-.35,.48]],.005,.95);ellipse(-.445,.48,.095,.025,.003,.88);ellipse(-.445,-.14,.155,.035,.004,.9);ellipse(-.445,-.185,.21,.043,.003,.68);
    curve([-.48,.42],[[-.47,.21,-.40,.19,-.42,.41]],.0026,.7);line([[-.445,.49],[-.44,.54]],.003,.96);
    curve([-.442,.73],[[-.56,.56,-.49,.53,-.442,.54],[-.38,.55,-.385,.63,-.442,.73]],.0045,.95);
    for(let i=1;i<5;i++)ellipse(-.444,.617,.035+i*.025,.083+i*.031,.0012,.12);
    dot(-.446,.592,.018,.52);
  }
  function person(d,x,y,scale,facing){
    const{line,curve,ellipse}=d;const t=p=>[x+p[0]*scale,y+p[1]*scale];
    ellipse(...t([0,.27]),.034*scale,.049*scale,.003,.22,true,-.1*facing);
    const face=[[-.026,.302],[.010,.316],[.030,.291],[.039,.268],[.055,.260],[.035,.25],[.025,.222],[-.010,.22],[-.029,.247],[-.035,.275]];
    line(face.map(p=>t([p[0]*facing,p[1]])),.0035,.94,true);
    for(let j=0;j<7;j++)line([[-.03+j*.008,.292+Math.sin(j*.5)*.01],[-.026+j*.006,.312+Math.sin(j*.5)*.005]].map(p=>t([p[0]*facing,p[1]])),.002,.64);
    const coat=[[-.025,.22],[-.061,.17],[-.072,.03],[-.096,-.115],[-.055,-.13],[.054,-.123],[.081,-.1],[.047,.07],[.053,.15],[.025,.22]];
    line(coat.map(t),.003,.13,true,true);line(coat.map(t),.004,.95,true);
    line([[-.038,-.12],[-.045,-.26],[-.057,-.29],[-.008,-.29],[.007,-.13]].map(t),.004,.96);
    line([[.019,-.125],[.031,-.275],[.045,-.29],[.079,-.29],[.060,-.26],[.054,-.125]].map(t),.004,.96);
    const arm=[[facing*.047,.16],[facing*.074,.06],[facing*.105,.055],[facing*.14,.045]];
    line(arm.map(t),.010,.86);line([[facing*.142,.045],[facing*.18,.046]].map(t),.005,.84);
    curve(t([-.032,.17]),[[x-.036*scale,y+.08*scale,x-.002*scale,y-.04*scale,x-.053*scale,y-.11*scale]],.0018,.55);
    line([[.006,.19],[.012,-.1]].map(t),.0019,.8);
    line([[-.025,.20],[.006,.14],[.028,.198]].map(t),.0024,.84);
    for(let j=0;j<8;j++)line([[-.052+j*.013,-.115],[-.025+j*.007,.05]].map(t),.0011,.38);
  }
  function lastDawn(d,includeNear=true){
    const{line,curve,ellipse}=d;
    // The duel is suggested at a distance; there is no impact, wound or blood.
    ellipse(.02,.10,.30,.30,.0024,.43);ellipse(.02,.10,.335,.335,.0017,.25);
    const random=rng(18320530);
    for(let j=0;j<27;j++){
      const y=-.05+j*.019,span=Math.sqrt(Math.max(0,.32*.32-(y-.1)*(y-.1)));
      if(span>0)line([[.02-span,y],[.02+span,y]],.0011,.12);
    }
    curve([-.83,-.17],[[-.48,-.08,-.18,-.23,.08,-.15],[.40,-.09,.63,-.23,.84,-.15]],.003,.58);
    for(let j=0;j<8;j++){const y=-.31-j*.055;curve([-.82+random()*.08,y],[[ -.35,y+.038,.15,y-.038,.82-random()*.11,y+.014]],.0015,.27-j*.019);}
    if(includeNear)person(d,-.43,-.21,1.03,1);person(d,.47,-.16,.87,-1);
    // Sparse winter branches frame the dawn, leaving the figures legible.
    for(const side of[-1,1]){
      const x=.76*side;curve([x,-.27],[[x-.015*side,.04,x+.024*side,.28,x-.025*side,.60]],.004,.5);
      for(let j=0;j<5;j++){const y=.05+j*.095;curve([x,y],[[x-.04*side,y+.055,x-.10*side,y+.05,x-.15*side,y+.15]],.0018,.37);}
    }
    // A shrinking series of luminous ripples carries the brief-life metaphor.
    for(let j=0;j<4;j++)ellipse(-.43,-.535-j*.018,.14+j*.029,.011+j*.005,.0012,.34-j*.065);
    for(let j=0;j<12;j++){const a=j*Math.PI/11;line([[.02+.35*Math.cos(a),.10+.35*Math.sin(a)],[.02+.39*Math.cos(a),.10+.39*Math.sin(a)]],.0014,.17);}
  }
  const leafDesigns=Object.freeze([
    {tag:2,x:-.68,y:.70,size:.153,angle:-.46},
    {tag:3,x:-.15,y:.83,size:.130,angle:.60},
    {tag:4,x:.49,y:.73,size:.157,angle:1.06},
    {tag:5,x:.75,y:.14,size:.148,angle:-.40},
    {tag:6,x:.57,y:-.57,size:.139,angle:.74},
    {tag:7,x:-.65,y:-.64,size:.147,angle:-.79},
    {tag:8,x:-.75,y:-.035,size:.123,angle:1.48}
  ].map(Object.freeze));
  const leaves=Object.freeze(leafDesigns.map(l=>Object.freeze({tag:l.tag,centre:Object.freeze([l.x,l.y-.035]),radius:l.size*1.3})));
  function autumnLeaf(d,leaf){
    const{line,curve}=d,c=Math.cos(leaf.angle),s=Math.sin(leaf.angle);
    const t=p=>[leaf.x+leaf.size*(c*p[0]-s*p[1]),leaf.y+leaf.size*(s*p[0]+c*p[1])];
    const map=p=>p.length===4?[...t(p.slice(0,2)),...t(p.slice(2,4))]:[...t(p.slice(0,2)),...t(p.slice(2,4)),...t(p.slice(4,6))];
    if(leaf.tag%2===0){
      // Rounded oak lobes read as leaves even at the wide establishing view.
      const side=[[0,1],[.13,.80],[.28,.88],[.34,.75],[.20,.62],[.42,.69],[.49,.54],[.30,.42],[.53,.40],[.55,.25],[.29,.13],[.49,.035],[.46,-.12],[.23,-.16],[.34,-.34],[.22,-.49],[.095,-.50],[0,-.88]];
      const outline=[...side,...side.slice(1,-1).reverse().map(p=>[-p[0],p[1]])].map(t);
      const path=()=>{d.ctx.beginPath();const last=outline[outline.length-1],first=outline[0];d.ctx.moveTo((last[0]+first[0])/2,(last[1]+first[1])/2);outline.forEach((p,i)=>{const next=outline[(i+1)%outline.length];d.ctx.quadraticCurveTo(p[0],p[1],(p[0]+next[0])/2,(p[1]+next[1])/2);});d.ctx.closePath();};
      d.style(.002,.083);path();d.ctx.fill();d.style(.0028,.89);path();d.ctx.stroke();
      curve(t([0,-.88]),[map([.045,-.12,-.04,.55,0,1])],.0017,.84);
      for(const side of[-1,1])for(const p of[[.27,.79],[.42,.59],[.46,.30],[.40,-.045],[.26,-.37]])curve(t([0,p[1]-.21]),[map([side*p[0]*.33,p[1]-.11,side*p[0]*.72,p[1]-.03,side*p[0],p[1]])],.00125,.64);
    }else{
      const outline=[];for(let j=0;j<=16;j++){const u=j/16,y=1-u*1.87,w=Math.sin(Math.PI*u)*.48;outline.push([w*(j%2?.88:1.05),y]);}for(let j=16;j>=0;j--){const u=j/16,y=1-u*1.87,w=Math.sin(Math.PI*u)*.48;outline.push([-w*(j%2?.88:1.05),y]);}
      line(outline.map(t),.002,.076,true,true);line(outline.map(t),.0028,.87,true);
      curve(t([0,-.88]),[map([.04,-.12,-.07,.40,0,1])],.0017,.82);
      for(let j=1;j<8;j++){const y=-.70+j*.19,w=Math.sin(Math.PI*(1-y)/1.87)*.44;for(const side of[-1,1])curve(t([0,y-.13]),[map([side*w*.48,y-.05,side*w*.86,y+.02,side*w,y+.055])],.0012,.60);}
    }
    curve(t([0,-.86]),[map([.02,-1.03,.06,-1.10,.025,-1.24])],.0021,.76);
  }
  function echoes(d){
    const{line,curve,ellipse,dot}=d;
    // One ageing manuscript. Its uneven edges and rolled corners carry time;
    // the ink remains while individually tagged autumn leaves pass over it.
    const parchment=[[-.53,.54],[-.33,.552],[-.14,.525],[.06,.542],[.23,.526],[.43,.50],[.47,.345],[.46,.12],[.49,-.08],[.47,-.30],[.48,-.535],[.59,-.668],[.36,-.681],[.14,-.702],[-.07,-.694],[-.28,-.733],[-.475,-.700],[-.53,-.543],[-.505,-.32],[-.526,-.12],[-.51,.10],[-.535,.31]];
    line(parchment,.002,.030,true,true);line(parchment,.0043,.83,true);
    curve([.429,.502],[[.54,.55,.652,.487,.646,.412],[.651,.359,.555,.327,.472,.345]],.004,.85);
    curve([.484,.492],[[.615,.49,.615,.397,.515,.373]],.0025,.61);
    curve([.480,-.536],[[.507,-.612,.537,-.631,.59,-.668]],.002,.46);
    curve([-.475,-.700],[[-.615,-.719,-.659,-.616,-.576,-.57],[-.548,-.56,-.509,-.592,-.501,-.643]],.0033,.77);
    curve([-.584,-.66],[[-.61,-.607,-.55,-.592,-.523,-.625]],.002,.50);
    // Handwritten clauses and mathematical working, not a typographic label.
    const random=rng(18431846);
    for(let row=0;row<18;row++){
      const y=.412-row*.050,x0=-.413+random()*.014,words=3+(row%3);
      let x=x0;
      for(let word=0;word<words;word++){
        const length=.087+random()*.055;
        const end=Math.min(.37,x+length);
        curve([x,y],[[x+.02,y+.014,x+.030,y-.018,x+.043,y+.004],[x+.061,y+.022,end-.018,y-.018,end,y+.003]],.0016,row<3?.76:.58);
        if(row%4===1)line([[x+.01,y+.016],[x+.043,y+.009]],.0011,.43);
        x=end+.025+random()*.012;
      }
    }
    // A small root-permutation sketch breaks the texture of the writing.
    const ring=[[-.11,-.50],[-.015,-.445],[.080,-.50],[.047,-.602],[-.076,-.602]];
    for(let i=0;i<5;i++){line([ring[i],ring[(i+2)%5]],.0016,.55);ellipse(...ring[i],.009,.009,.0018,.66);}
    for(let j=0;j<5;j++){const y=.32-j*.178;line([[-.49,y],[-.477,y-.038]],.0011,.29);line([[.438,y-.072],[.445,y-.12]],.0011,.26);}
    // A sparse branch frames the falling leaves without closing the scene.
    curve([-.91,.67],[[-.70,.78,-.45,.81,-.18,.915],[.08,.955,.31,.88,.65,.91]],.0026,.37);
    curve([-.63,.807],[[-.61,.9,-.51,.925,-.47,.978]],.0015,.29);
    curve([.34,.91],[[.41,.82,.56,.836,.66,.76]],.0015,.30);
    for(let j=0;j<14;j++){const x=-.46+j*.067;dot(x,-.81+Math.sin(j*.74)*.014,.002,.23);}
  }
  const renderers=[null,awakening,symmetries,prison,letter,lastDawn,echoes];
  const motifCache=new Map();
  function motifPixels(index){
    if(motifCache.has(index))return motifCache.get(index);
    const d=drawing(),layers=[{drawing:d,tag:0}];
    if(index===5){
      // Separate layers retain the landscape even behind the figure. A tiny
      // depth marker identifies this figure's own grains for the musical fade;
      // no bounding box can accidentally erase the horizon or the other man.
      lastDawn(d,false);
      const near=drawing();person(near,-.43,-.21,1.03,1);
      layers.push({drawing:near,tag:1});
    }else if(index===6){
      echoes(d);
      for(const leaf of leafDesigns){const layer=drawing();autumnLeaf(layer,leaf);layers.push({drawing:layer,tag:leaf.tag});}
    }else renderers[index](d);
    const pixels=[],weights=[];let total=0;
    for(const layer of layers){
      const image=layer.drawing.ctx.getImageData(0,0,d.size,d.size).data;
      for(let y=0;y<d.size;y++)for(let x=0;x<d.size;x++){
        const alpha=image[(y*d.size+x)*4+3];if(alpha<8)continue;
        // Lower-opacity engraving fills remain soft, never solid gold blocks.
        total+=Math.pow(alpha/255,1.30);pixels.push(x,y,alpha/255,layer.tag);weights.push(total);
      }
    }
    const result={pixels:new Float32Array(pixels),weights:new Float32Array(weights),total,size:d.size,scale:d.scale};
    if(!weights.length)throw new Error('Galois tableau contains no grains');motifCache.set(index,result);return result;
  }
  function sampleNode(count,index=0){
    index=Math.max(0,Math.min(nodes.length-1,Math.floor(index)));if(index===0)return sample(count);
    const data=motifPixels(index),random=rng(18110000+index*7919),points=[];
    for(let i=0;i<count;i++){
      const pick=random()*data.total;let lo=0,hi=data.weights.length-1;
      while(lo<hi){const mid=(lo+hi)>>>1;if(data.weights[mid]<pick)lo=mid+1;else hi=mid;}
      const at=lo*4,x=(data.pixels[at]+random()-data.size/2)/data.scale,y=(data.size/2-data.pixels[at+1]-random())/data.scale;
      points.push([x,y-.035,.014*data.pixels[at+2]+(random()-.5)*.003+.03*data.pixels[at+3]]);
    }
    return pack(points,count,[count,0,0]);
  }
  window.CourseOpeningGalois=Object.freeze({sample,sampleNode,nodeCount:nodes.length,nodes,leaves,evidence:()=>({name:'Évariste Galois',born:1811,died:1832,inscription:'Évariste Galois',dates:'1811–1832',portraitArtist:'Alfred Galois',portraitPublished:1848,letterStrokeScale:1/3,portraitVerticalShift:-.09,nodeCount:nodes.length,nodes,leaves})});
})();
