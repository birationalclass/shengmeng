# 数学难民营 — A retreat for wandering minds

An original, navigable 3D architectural scene for Sheng Meng's Visual Lab. **Not a video, image panorama, or 2.5D photo displacement.** The structure, rooms, furniture, plants, pool and surrounding terrain are modeled geometry. This is an initial reference-inspired scene, not a verified pixel-equivalent reconstruction of the supplied film.

## Reference and camera design

Reference: [梦境之初q — 刷到就说明你未来将会拥有这样的房子](https://www.bilibili.com/video/BV1umun6PEvs/), 8:09, posted 2026-08-06, labelled as including AI-generated content by Bilibili. Initial access returned 412; a later ordinary browser opening succeeded. Observed opening material includes a layered dark-framed glass hillside villa, terraces, a reflecting-water passage with stone steps, warm linear lighting, an atrium and window-side interiors. We have **not** extracted the original camera tracks, underlying models or material maps, nor verified every shot of the full film. No original frames, audio or models are redistributed.

The seven-chapter tour uses arc-length sampled Catmull–Rom camera and target curves with eased movement: coastal arrival, low pool-side dolly, library, conference room, a dedicated chalkboard lesson, ocean terrace and rising retreat. The lesson camera follows the active board pair with a damped, level close view. Each chapter has its own position, target and field of view. Chapter transitions fade, manual dragging stops the tour, and resume blends back (long relocations fade rather than fly through walls). These are inspired camera categories, **not motion capture from the reference**.

## Rendering and modeling

- Complete geometric, multi-level architecture: slabs, vertical fins, mullions, open loggias, stairs and railings; rounded upholstery, tables, modeled books, brass torus-knot sculpture and mathematical blackboard.
- Expanded into two offset building wings: a 20 × 20 ground-floor conference hall with 14 modeled chairs, a glazed connecting gallery, set-back upper discussion pavilion, external stair, roof garden and an 11 × 26 cliffside viewing deck. Ocean-facing doors are actual gaps in the glazing. Overall footprint extends from x = −16.5 to x = 49 instead of ending at x = 16.5.
- An 8,000-unit procedural ocean with animated multi-scale water normals, Fresnel horizon color and sun glitter. Terrain drops below water beyond the east cliff, vegetation stays ashore and mountains are confined to the landward side. The ocean intentionally uses an analytic shader, not another planar-reflection camera, avoiding recursive reflection passes with the courtyard pool. Its surface is planar; it is not a hydrodynamic simulation or ray-traced ocean.
- Physically based wood and marble material maps, normal/roughness detail, physical glass material, PMREM sky lighting, shadow maps, ACES tone mapping, restrained bloom and multisample render targets.
- A rendered planar reflection camera with animated water normals; reflections change with the live viewpoint. This is not ray-traced refraction or a fluid simulation.
- Seeded instancing batches for repeated elements and vegetation; finite terrain grid and mountains; capped pixel ratio and a lighter rendering setting. No frame-rate target is claimed without browser/device testing.
- Free observation with OrbitControls, touch pinch/pan and keyboard translation; **no collision-controlled walking physics**. Users can pass through geometry in free observation.
- Fullscreen, hideable controls, light adjustment, tour speed and reduced-motion support. No autoplay audio.
- Entrance lintel and stair-side signs read “数学难民营”. Two independent chalkboards describe the unforced periodic 3D Navier–Stokes global smoothness question and the rational Hodge conjecture (with a question mark). The NS board has a large translucent “NS” background split into twelve displaced, clipped fragments beneath the legible foreground text. The text states the questions, not a claim about research status. Formulations: [Clay NS statement](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf), [Clay Hodge conjecture](https://www.claymath.org/millennium/hodge-conjecture/).

## Six-board spectral-sequence classroom

The conference room has three independent pairs of counter-moving boards, six surfaces total, each with its own canvas texture. Two depth-separated rails let the boards pass while exchanging upper/lower positions. The sequence writes across the three lower boards, lowers the other boards in turn and preserves the previous work above. On reuse, a visible eraser sweeps alternating strips before new writing begins. Grain stays deterministic rather than flickering. Row-wise reveal preserves real SVG mathematical layout; it is a chalk-writing effect, **not reconstructed human handwriting strokes**.

`build-chalk-notes.mjs` reads the existing `study/spectral` exports and converts their formulas into 65 local SVG pages using build-only MathJax 3.2.2. Pages cover double complexes, filtrations, convergence, Hodge and Leray; the manifest retains the source TeX and section. They reproduce the exported main formula content with short context, not every proof-dialog derivation or interactive diagram. The classroom links back to the original notebook for full statements, proofs and interactions. No runtime CDN is needed. SVG formula paths avoid depending on installed mathematical fonts; Chinese labels use system Kai-style/Chinese fallbacks. See [MathJax server integration](https://docs.mathjax.org/en/v3.2/server/direct.html).

Controls: select any page, previous/next, pause/resume writing, erase/rewrite, focus the lesson camera, and slide or exchange each board pair. Manual lifting pauses writing. Reduced-motion mode displays complete static pages; page controls and direct lifts still work. Hidden tabs do not advance the lesson. Loading failures appear in the classroom status.

To regenerate with the pinned extracted `mathjax-full` package: `node visuals/math-refuge/build-chalk-notes.mjs /path/to/mathjax-full-3.2.2`. MathJax's license is included under `assets/chalk/`.

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

Run `node --test visuals/math-refuge/checks.test.mjs`. Covers seven camera chapters, imports/local assets, geometry assembly and finite buffers, coastline elevations, source SVG page bounds, six-slot scheduling including erase/reuse/wraparound, classroom assembly, independent textures, pause/lift controls and reduced-motion pages. Uses real Three.js geometry classes with mocked texture/PMREM/canvas/image services. It does not compile GPU shaders or test browser interactions. Browser/visual checks intentionally omitted at the user's request.
