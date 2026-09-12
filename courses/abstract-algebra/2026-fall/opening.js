(() => {
  'use strict';
  const dialog = document.getElementById('courseOpening');
  const root = document.getElementById('symmetry-particle-studies');
  const canvas = root.querySelector('canvas');
  const caption = root.querySelector('.opening-caption');
  const pending = document.documentElement.classList;
  let film = null;
  let initialization = null;

  function leaveOpening() {
    if (film) film.stop();
    if (dialog.open) dialog.close();
    document.body.classList.remove('opening-active');
    pending.remove('course-opening-pending');
    const main = document.getElementById('main');
    main.setAttribute('tabindex', '-1');
    main.focus({ preventScroll: true });
  }

  async function openOpening() {
    if (dialog.open) return;
    dialog.showModal();
    dialog.focus({ preventScroll: true });
    document.body.classList.add('opening-active');
    pending.remove('course-opening-pending');
    try {
      if (!initialization) initialization = initialize();
      await initialization;
      if (dialog.open) film.play();
    } catch (error) {
      // The course remains accessible if graphics initialization is unavailable.
      root.dataset.unavailable = 'true';
      leaveOpening();
    }
  }

  dialog.addEventListener('click', leaveOpening);
  dialog.addEventListener('keydown', event => {
    if ((event.key === 'Enter' || event.key === ' ') && !event.repeat) {
      event.preventDefault();
      leaveOpening();
    }
  });
  dialog.addEventListener('cancel', event => {
    event.preventDefault();
    leaveOpening();
  });
  document.querySelector('[data-replay-opening]').addEventListener('click', openOpening);

  const paint = () => new Promise(resolve => requestAnimationFrame(resolve));

  async function initialize() {
    const geometry = window.CourseOpeningGeometry;
    const gl = canvas.getContext('webgl', { alpha: false, antialias: false, preserveDrawingBuffer: true });
    if (!gl || !geometry) throw new Error('Opening unavailable');
    const N = geometry.count;
    const targets = [];
    for (let i = 0; i < geometry.captions.length; i++) {
      targets.push(geometry.create(i));
      root.dataset.prepared = String(i + 1);
      await paint();
    }
    const vertex = `precision highp float;
      attribute vec2 start; attribute vec2 finish; attribute vec4 grain;
      uniform float progress; uniform float aspect; uniform float dpr;
      varying vec3 color; varying float opacity; varying float facet;
      void main(){
        float t=progress; float e=t*t*t*(t*(t*6.-15.)+10.);
        vec2 delta=finish-start; float arch=sin(3.14159265359*e);
        vec2 p=mix(start,finish,e)+vec2(-delta.y,delta.x)*arch*.28;
        float dist=length(delta);
        p+=vec2(sin(grain.x*19.+e*6.283),cos(grain.y*23.-e*6.283))*arch*min(.022,dist*.16);
        float fit=min(.68,aspect*.84); p*=fit;
        p.y+=mix(.05,.20,smoothstep(.8,1.3,aspect)); p.x/=aspect;
        gl_Position=vec4(p,0.,1.); gl_PointSize=(.8+grain.z*1.5)*dpr;
        float light=.74+.26*clamp(1.-length(p-vec2(-.35,.48))*.5,0.,1.);
        vec3 base=mix(vec3(.46,.33,.16),vec3(.91,.77,.49),grain.w);
        base=mix(base,vec3(.99,.91,.74),pow(grain.y,18.)*.66);
        color=base*light; opacity=.65+.30*grain.x; facet=grain.z;
      }`;
    const fragment = `precision mediump float;
      varying vec3 color; varying float opacity; varying float facet;
      void main(){vec2 p=gl_PointCoord*2.-1.;float r=length(p*vec2(1.,.84+facet*.22));
        if(r>1.)discard;float edge=1.-smoothstep(.25,1.,r);
        float shading=.74+.26*clamp(.5-p.x*.5+p.y*.2,0.,1.);
        gl_FragColor=vec4(color*shading,edge*opacity);}`;
    const bgv = 'attribute vec2 pos;varying vec2 uv;void main(){uv=pos;gl_Position=vec4(pos,0.,1.);}';
    const bgf = `precision highp float;varying vec2 uv;
      float hash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7)))*43758.5453);}
      void main(){float noise=hash(floor(gl_FragCoord.xy))*.009;
        float lamp=exp(-length((uv-vec2(-.5,.45))*vec2(.7,1.)))*.015;
        float v=1.-smoothstep(.25,1.5,length(uv));
        gl_FragColor=vec4(vec3(.018,.017,.014)+vec3(.6,.49,.28)*(lamp+noise)*v,1.);}`;
    function compile(type, source) {
      const shader = gl.createShader(type);
      gl.shaderSource(shader, source); gl.compileShader(shader);
      if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(shader));
      return shader;
    }
    function link(v, f) {
      const program = gl.createProgram();
      gl.attachShader(program, compile(gl.VERTEX_SHADER, v));
      gl.attachShader(program, compile(gl.FRAGMENT_SHADER, f));
      gl.linkProgram(program);
      if (!gl.getProgramParameter(program, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(program));
      return program;
    }
    function buffer(data, usage) {
      const result = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, result);
      gl.bufferData(gl.ARRAY_BUFFER, data, usage); return result;
    }
    const program = link(vertex, fragment), background = link(bgv, bgf);
    const quad = buffer(new Float32Array([-1,-1,1,-1,-1,1,-1,1,1,-1,1,1]), gl.STATIC_DRAW);
    let source = targets[0].slice(), destination = targets[0];
    const sourceBuffer = buffer(source, gl.DYNAMIC_DRAW), destinationBuffer = buffer(destination, gl.DYNAMIC_DRAW);
    let seed = 317129;
    const grains = new Float32Array(N * 4);
    for (let i = 0; i < grains.length; i++) {
      seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
      grains[i] = seed / 4294967296;
    }
    const grainBuffer = buffer(grains, gl.STATIC_DRAW);
    const loc = {
      source: gl.getAttribLocation(program, 'start'), destination: gl.getAttribLocation(program, 'finish'),
      grain: gl.getAttribLocation(program, 'grain'), progress: gl.getUniformLocation(program, 'progress'),
      aspect: gl.getUniformLocation(program, 'aspect'), dpr: gl.getUniformLocation(program, 'dpr'),
      quad: gl.getAttribLocation(background, 'pos')
    };
    function attribute(data, location, size) {
      gl.bindBuffer(gl.ARRAY_BUFFER, data); gl.enableVertexAttribArray(location);
      gl.vertexAttribPointer(location, size, gl.FLOAT, false, 0, 0);
    }
    let scene = 0, progress = 1, moving = false, running = false, elapsed = 0, previous = 0, raf = 0;
    const holds = [4600, 4600, 4600, 7200, 8400];
    const ease = t => t*t*t*(t*(t*6-15)+10);
    function snapshot() {
      const e = ease(progress), arch = Math.sin(Math.PI * e), result = new Float32Array(N * 2);
      for (let i = 0; i < N; i++) {
        const k = i * 2, dx = destination[k] - source[k], dy = destination[k + 1] - source[k + 1];
        const drift = arch * Math.min(.022, Math.hypot(dx, dy) * .16);
        result[k] = source[k] + dx*e - dy*arch*.28 + Math.sin(grains[i*4]*19 + e*6.283)*drift;
        result[k+1] = source[k+1] + dy*e + dx*arch*.28 + Math.cos(grains[i*4+1]*23 - e*6.283)*drift;
      }
      return result;
    }
    function upload() {
      gl.bindBuffer(gl.ARRAY_BUFFER, sourceBuffer); gl.bufferSubData(gl.ARRAY_BUFFER, 0, source);
      gl.bindBuffer(gl.ARRAY_BUFFER, destinationBuffer); gl.bufferSubData(gl.ARRAY_BUFFER, 0, destination);
    }
    function updateCaption() {
      const text = geometry.captions[scene];
      root.querySelector('[data-caption-title]').textContent = text.title;
      root.querySelector('[data-caption-zh]').textContent = text.zh;
      root.querySelector('[data-caption-en]').textContent = text.en;
      canvas.setAttribute('aria-label', text.title + '。' + text.zh);
    }
    function draw() {
      const rect = canvas.getBoundingClientRect(), ratio = Math.min(2, window.devicePixelRatio || 1);
      const width = Math.max(1, Math.round(rect.width * ratio)), height = Math.max(1, Math.round(rect.height * ratio));
      if (canvas.width !== width || canvas.height !== height) { canvas.width = width; canvas.height = height; }
      gl.viewport(0, 0, width, height); gl.disable(gl.BLEND); gl.useProgram(background);
      attribute(quad, loc.quad, 2); gl.drawArrays(gl.TRIANGLES, 0, 6);
      gl.useProgram(program); attribute(sourceBuffer, loc.source, 2); attribute(destinationBuffer, loc.destination, 2);
      attribute(grainBuffer, loc.grain, 4); gl.enable(gl.BLEND); gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
      gl.uniform1f(loc.progress, progress); gl.uniform1f(loc.aspect, width / height);
      gl.uniform1f(loc.dpr, ratio * Math.max(1, Math.min(1.4, rect.height / 800)));
      gl.drawArrays(gl.POINTS, 0, N);
      root.dataset.scene = String(scene); root.dataset.progress = progress.toFixed(4);
    }
    function moveTo(index) {
      source = snapshot(); destination = targets[index]; scene = index;
      progress = 0; moving = true; elapsed = 0;
      caption.classList.remove('is-visible'); upload(); updateCaption(); draw();
    }
    function stop() { running = false; previous = 0; cancelAnimationFrame(raf); }
    function tick(now) {
      if (!running || !dialog.open) return;
      const dt = previous ? Math.min(100, now - previous) : 0;
      previous = now; elapsed += dt;
      if (moving) {
        progress = Math.min(1, elapsed / (scene === 4 ? 5200 : 4200)); draw();
        if (progress === 1) { moving = false; elapsed = 0; }
      } else {
        if (elapsed > 420) caption.classList.add('is-visible');
        if (elapsed > holds[scene] - 600 && scene < targets.length - 1) caption.classList.remove('is-visible');
        if (elapsed >= holds[scene]) {
          if (scene + 1 < targets.length) moveTo(scene + 1);
          else { stop(); return; }
        }
      }
      raf = requestAnimationFrame(tick);
    }
    function play() {
      stop(); source = targets[0].slice(); destination = targets[0]; scene = 0;
      progress = 1; moving = false; elapsed = 0; upload(); updateCaption(); draw();
      caption.classList.remove('is-visible');
      if (matchMedia('(prefers-reduced-motion: reduce)').matches) caption.classList.add('is-visible');
      else { running = true; raf = requestAnimationFrame(tick); }
    }
    film = { play, stop };
    // Authoring hooks allow deterministic stills and continuous-position checks without visible controls.
    root._openingPreview = {
      show(index) {
        stop(); scene = index; source = targets[index].slice(); destination = targets[index];
        progress = 1; moving = false; upload(); updateCaption(); draw(); caption.classList.add('is-visible');
      },
      transition(index, value) { stop(); moveTo(index); progress = value; draw(); },
      evidence() { return { count: N, scene, progress, positions: snapshot(), targets, geometry: geometry.evidence() }; }
    };
    document.addEventListener('visibilitychange', () => {
      previous = 0;
      if (document.hidden) cancelAnimationFrame(raf);
      else if (running && dialog.open) raf = requestAnimationFrame(tick);
    });
    canvas.addEventListener('webglcontextlost', event => { event.preventDefault(); leaveOpening(); });
    new ResizeObserver(draw).observe(canvas);
    updateCaption(); draw(); await paint();
    root.dataset.particleCount = String(N); root.dataset.ready = 'true';
    dialog.classList.add('opening-ready');
  }

  if (!location.hash && !window.courseOpeningDismissed) openOpening();
  else pending.remove('course-opening-pending');
})();
