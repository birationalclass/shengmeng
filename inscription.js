(()=>{
  const root=document.documentElement;
  const glyphNodes=[...document.querySelectorAll(".glyph-ink[data-char]")];
  const reducedMotion=window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  const svgNS="http://www.w3.org/2000/svg";
  let completed=false;
  let aborted=false;

  root.classList.remove("inscription-complete","inscription-fallback");

  const sleep=(ms)=>new Promise((resolve)=>window.setTimeout(resolve,ms));
  const svgElement=(name,attributes={})=>{
    const node=document.createElementNS(svgNS,name);
    Object.entries(attributes).forEach(([key,value])=>node.setAttribute(key,String(value)));
    return node;
  };
  const restoreStaticGlyphs=()=>glyphNodes.forEach((node)=>{
    node.classList.remove("is-vectorized","is-writing","is-carved");
    node.replaceChildren(document.createTextNode(node.dataset.char));
  });
  const finishIntro=()=>{
    if(completed)return;
    completed=true;
    root.classList.add("inscription-complete");
  };
  const abortIntro=()=>{
    if(completed)return;
    aborted=true;
    restoreStaticGlyphs();
    root.classList.add("inscription-fallback");
    finishIntro();
  };
  const failSafe=window.setTimeout(abortIntro,16000);

  const medianPath=(points)=>points.map((point,index)=>`${index?"L":"M"}${point[0]} ${900-point[1]}`).join(" ");

  const buildGlyph=(target,data,glyphIndex)=>{
    const svg=svgElement("svg",{
      class:"stroke-glyph",
      viewBox:"0 0 1024 1024",
      "aria-hidden":"true",
      focusable:"false"
    });
    const defs=svgElement("defs");
    svg.append(defs);

    const drawing=svgElement("g");
    const inkAttributes={
      x:"512",
      y:"520",
      "text-anchor":"middle",
      "font-family":"Zhi Mang Xing Title",
      "font-size":"820",
      "font-weight":"400"
    };
    const makeInk=(className)=>{
      const ink=svgElement("text",{class:className,...inkAttributes});
      ink.textContent=target.dataset.char;
      return ink;
    };
    drawing.append(makeInk("stroke-ink stroke-final"));
    const strokeEntries=[];

    data.strokes.forEach((_,index)=>{
      const maskId=`glyph-mask-${glyphIndex}-${index}`;
      const mask=svgElement("mask",{id:maskId,maskUnits:"userSpaceOnUse",x:"-140",y:"-180",width:"1300",height:"1260"});
      const reveal=svgElement("path",{
        class:"stroke-reveal",
        d:medianPath(data.medians[index]),
        fill:"none",
        stroke:"white",
        "stroke-width":"270",
        "stroke-linecap":"round",
        "stroke-linejoin":"round"
      });
      mask.append(reveal);
      defs.append(mask);

      const carvedStroke=svgElement("g",{class:"stroke-fragment-layer",mask:`url(#${maskId})`});
      carvedStroke.append(makeInk("stroke-ink stroke-fragment"));
      drawing.append(carvedStroke);
      strokeEntries.push({reveal,median:reveal});
    });

    const spark=svgElement("circle",{class:"stroke-spark",r:"22",cx:"0",cy:"0"});
    const sparkCore=svgElement("circle",{class:"stroke-spark-core",r:"7",cx:"0",cy:"0"});
    drawing.append(spark,sparkCore);
    svg.append(drawing);
    target.replaceChildren(svg);
    strokeEntries.forEach((entry)=>{
      entry.length=Math.max(1,entry.reveal.getTotalLength());
      entry.reveal.style.strokeDasharray=String(entry.length);
      entry.reveal.style.strokeDashoffset=String(entry.length);
    });
    target.classList.add("is-vectorized");
    return {target,svg,strokeEntries,spark,sparkCore};
  };

  const animateStroke=async(entry,spark,sparkCore)=>{
    const length=entry.length;
    const duration=Math.max(44,Math.min(96,length*.10));
    const drawing=entry.reveal.animate(
      [{strokeDashoffset:String(length)},{strokeDashoffset:"0"}],
      {duration,easing:"cubic-bezier(.32,.02,.22,1)",fill:"forwards"}
    );
    const start=performance.now();
    spark.style.opacity="1";
    sparkCore.style.opacity="1";
    await new Promise((resolve)=>{
      const advance=(now)=>{
        const progress=Math.min(1,(now-start)/duration);
        const point=entry.median.getPointAtLength(length*progress);
        spark.setAttribute("cx",point.x);
        spark.setAttribute("cy",point.y);
        sparkCore.setAttribute("cx",point.x);
        sparkCore.setAttribute("cy",point.y);
        if(progress<1)requestAnimationFrame(advance);else resolve();
      };
      requestAnimationFrame(advance);
    });
    await drawing.finished.catch(()=>{});
    entry.reveal.style.strokeDashoffset="0";
    drawing.cancel();
    spark.style.opacity="0";
    sparkCore.style.opacity="0";
    await sleep(6);
  };

  const run=async()=>{
    try{
      const data=await Promise.all(glyphNodes.map(async(node)=>{
        const response=await fetch(`assets/hanzi-strokes/${encodeURIComponent(node.dataset.char)}.json?v=20260812-uniform-running-script`);
        if(!response.ok)throw new Error(`Unable to load stroke data for ${node.dataset.char}`);
        return response.json();
      }));
      await document.fonts.load('400 820px "Zhi Mang Xing Title"');
      if(aborted)return;
      const glyphs=glyphNodes.map((node,index)=>buildGlyph(node,data[index],index));
      if(reducedMotion){
        glyphs.forEach((glyph)=>{
          glyph.target.classList.add("is-carved");
          glyph.svg.querySelectorAll(".stroke-fragment-layer").forEach((layer)=>layer.remove());
        });
        await sleep(120);
        finishIntro();
        return;
      }
      await sleep(420);
      for(const glyph of glyphs){
        if(aborted)return;
        glyph.target.classList.add("is-writing");
        for(const stroke of glyph.strokeEntries){
          if(aborted)return;
          await animateStroke(stroke,glyph.spark,glyph.sparkCore);
        }
        glyph.target.classList.remove("is-writing");
        glyph.target.classList.add("is-carved");
        await sleep(110);
        glyph.svg.querySelectorAll(".stroke-fragment-layer").forEach((layer)=>layer.remove());
        await sleep(14);
      }
      await sleep(260);
      finishIntro();
    }catch(error){
      if(aborted)return;
      console.warn("Calligraphy intro fallback:",error);
      aborted=true;
      restoreStaticGlyphs();
      root.classList.add("inscription-fallback");
      await sleep(320);
      finishIntro();
    }finally{
      window.clearTimeout(failSafe);
    }
  };

  run();
})();
