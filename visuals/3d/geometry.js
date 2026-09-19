// Depth is normalized inverse depth: near = 1, far = 0.
export function sampleDepth(depth, u, v) {
  const x = Math.min(depth.width - 1, Math.max(0, u * (depth.width - 1)));
  const y = Math.min(depth.height - 1, Math.max(0, v * (depth.height - 1)));
  const x0 = Math.floor(x), y0 = Math.floor(y);
  const x1 = Math.min(x0 + 1, depth.width - 1), y1 = Math.min(y0 + 1, depth.height - 1);
  const a = depth.values[y0 * depth.width + x0] * (1 - (x - x0)) + depth.values[y0 * depth.width + x1] * (x - x0);
  const b = depth.values[y1 * depth.width + x0] * (1 - (x - x0)) + depth.values[y1 * depth.width + x1] * (x - x0);
  return a * (1 - (y - y0)) + b * (y - y0);
}
export function createRelief(depth, aspect, resolution, strength, invert, cameraDistance) {
  const nx = Math.max(30, Math.round(resolution * Math.min(1, aspect)));
  const ny = Math.max(30, Math.round(resolution * Math.min(1, 1 / aspect)));
  const count = (nx + 1) * (ny + 1);
  const positions = new Float32Array(count * 3), uvs = new Float32Array(count * 2), values = new Float32Array(count);
  const w = aspect >= 1 ? 4.2 : 4.2 * aspect, h = w / aspect;
  for (let y = 0; y <= ny; y++) for (let x = 0; x <= nx; x++) {
    const i = y * (nx + 1) + x, u = x / nx, v = y / ny;
    const d = sampleDepth(depth, u, v);
    const z = ((invert ? 1 - d : d) - .5) * strength * 1.9;
    const perspective = (cameraDistance - z) / cameraDistance;
    positions.set([(u - .5) * w * perspective, (.5 - v) * h * perspective, z], i * 3);
    uvs.set([u, 1 - v], i * 2);
    values[i] = d;
  }
  const indices = [];
  const triangle = (a, b, c) => {
    // Cut occlusion boundaries instead of stretching texture across foreground gaps.
    if (!depth.ai || Math.max(values[a], values[b], values[c]) - Math.min(values[a], values[b], values[c]) < .18 || strength < .01) indices.push(a, b, c);
  };
  for (let y = 0; y < ny; y++) for (let x = 0; x < nx; x++) {
    const a = y * (nx + 1) + x, b = a + 1, c = a + nx + 1, d = c + 1;
    triangle(a, c, b); triangle(b, c, d);
  }
  return { positions, uvs, indices, count };
}

// Original procedural landscape. Its analytic depth is a demo, never labelled AI.
export function createDemo() {
  const canvas = document.createElement('canvas');
  canvas.width = 960; canvas.height = 720;
  const ctx = canvas.getContext('2d');
  const pixels = ctx.createImageData(canvas.width, canvas.height);
  const values = new Float32Array(canvas.width * canvas.height);
  const colours = [[181,202,162],[119,159,127],[77,129,108],[211,175,120],[172,130,84],[78,112,79]];
  for (let y = 0; y < canvas.height; y++) for (let x = 0; x < canvas.width; x++) {
    const u = x / canvas.width, v = y / canvas.height;
    const ridges = [.34 + .055*Math.sin(u*8) + .028*Math.sin(u*23), .48+.12*Math.sin(u*5+1)+.02*Math.sin(u*22), .62+.09*Math.sin(u*7+3), .72+.11*Math.sin(u*5+5), .9+.05*Math.sin(u*9)];
    let layer = 0;
    for (const ridge of ridges) if (v > ridge) layer++;
    const i = y*canvas.width+x;
    let d = layer === 0 ? .04 : .11+layer*.14+(v-(ridges[layer-1] || 0))*.18;
    let rgb = colours[layer];
    let shading = 1 + .045*Math.sin(u*17+v*13) + .015*Math.sin(u*160+v*70);
    if (layer === 0) {
      shading = 1.02-v*.13;
      if (Math.hypot((u-.68)*canvas.width,(v-.2)*canvas.height) < 44) { rgb=[242,225,182]; shading=1; d=.045; }
    } else shading += .04*Math.sin(u*8+layer);
    for (let c = 0; c < 3; c++) pixels.data[i*4+c] = Math.min(255,rgb[c]*shading);
    pixels.data[i*4+3]=255; values[i]=Math.min(1,d);
  }
  ctx.putImageData(pixels,0,0);
  return { canvas, depth:{width:canvas.width,height:canvas.height,values} };
}
