# 数学难民营 — A retreat for wandering minds

An original, navigable 3D architectural scene for Sheng Meng's Visual Lab. **Not a video, image panorama, or 2.5D photo displacement.** The structure, rooms, furniture, plants, pool and surrounding terrain are modeled geometry. This is an initial reference-inspired scene, not a verified pixel-equivalent reconstruction of the supplied film.

## Reference and camera design

Reference: [梦境之初q — 刷到就说明你未来将会拥有这样的房子](https://www.bilibili.com/video/BV1umun6PEvs/), 8:09, posted 2026-08-06, labelled as including AI-generated content by Bilibili. Initial access returned 412; a later ordinary browser opening succeeded. Observed opening material includes a layered dark-framed glass hillside villa, terraces, a reflecting-water passage with stone steps, warm linear lighting, an atrium and window-side interiors. We have **not** extracted the original camera tracks, underlying models or material maps, nor verified every shot of the full film. No original frames, audio or models are redistributed.

The original five-shot tour uses arc-length sampled Catmull–Rom camera and target curves with eased movement: aerial arrival (24 s), low pool-side dolly (22 s), interior glide (26 s), terrace track (24 s) and rising retreat (26 s). Each has its own position, target and field of view. Chapter transitions fade, manual dragging stops the tour, and resume blends back (long relocations fade rather than fly through walls). These are inspired camera categories, **not motion capture from the reference**.

## Rendering and modeling

- Complete geometric, multi-level architecture: slabs, vertical fins, mullions, open loggias, stairs and railings; rounded upholstery, tables, modeled books, brass torus-knot sculpture and mathematical blackboard.
- Physically based wood and marble material maps, normal/roughness detail, physical glass material, PMREM sky lighting, shadow maps, ACES tone mapping, restrained bloom and multisample render targets.
- A rendered planar reflection camera with animated water normals; reflections change with the live viewpoint. This is not ray-traced refraction or a fluid simulation.
- Seeded instancing batches for repeated elements and vegetation; finite terrain grid and mountains; capped pixel ratio and a lighter rendering setting. No frame-rate target is claimed without browser/device testing.
- Free observation with OrbitControls, touch pinch/pan and keyboard translation; **no collision-controlled walking physics**. Users can pass through geometry in free observation.
- Fullscreen, hideable controls, light adjustment, tour speed and reduced-motion support. No autoplay audio.

### Contemporary techniques considered

Primary documentation reviewed on 2026-09-19:

- [Three.js WebGPURenderer](https://threejs.org/docs/pages/WebGPURenderer.html): modern WebGPU backend with WebGL2 fallback. Not enabled here: this project currently shares pinned Three.js 0.180.0 WebGL addons and planar-reflection materials. Calling this module WebGPU-rendered would be incorrect.
- [Spark Gaussian splat LoD](https://sparkjs.dev/docs/lod-getting-started/): streamed/adaptive splat rendering can support detailed captured environments. No training-ready, geometrically consistent capture or splat asset was supplied, so Gaussian splatting is not used or simulated by ordinary points.
- [three-gpu-pathtracer](https://github.com/gkjohnson/three-gpu-pathtracer): progressive physically based path tracing. Not included in this version: convergence during continuous travel and target-device performance require a separate validation pass. Current lighting is rasterized PBR with planar reflection, not full path tracing/global illumination.

The requested goal “quality and detail no lower than the video” remains **unverified and not claimed achieved**. Matching every reference room and close-up would require more asset detail and visual comparison. The user explicitly selected code checks only for this iteration, so no browser interaction/visual acceptance is performed.

## Assets and licenses

- Three.js 0.180.0 addons downloaded from the official package distribution on jsDelivr, MIT. Existing core/OrbitControls and the MIT license are reused from `../3d/vendor/THREE-LICENSE.txt`.
- Water normal texture: [Three.js r180 example asset](https://github.com/mrdoob/three.js/blob/r180/examples/textures/waternormals.jpg).
- [Poly Haven wood_floor_deck](https://polyhaven.com/a/wood_floor_deck) and [marble_01](https://polyhaven.com/a/marble_01): 1K diffuse, OpenGL normal and roughness JPGs, [CC0](https://polyhaven.com/license). Served locally; no user images leave the device.
- Geometry, layout and camera choreography are original to this module. Reference author credited for visual direction, with no claim of endorsement.

`fetch-assets.mjs` reproducibly retrieves pinned library dependencies and these public materials. No build step; serve the repository root over HTTP and open `/visuals/math-refuge/`. All runtime assets are local.

## Code verification

Run `node --test visuals/math-refuge/checks.test.mjs`. Covers shot timing/bounds and finite camera paths, asset/import references and modeled-scene assembly using real Three.js geometry classes with mocked texture/PMREM/canvas services. It does not compile GPU shaders or test browser interactions. Browser/visual checks intentionally omitted at the user's request.
