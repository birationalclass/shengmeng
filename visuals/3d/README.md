# 3D化 · Spatial Studio

Static GitHub Pages application: upload JPEG/PNG/WebP, run Depth Anything V2 Small locally in a module worker, reconstruct a textured 2.5D mesh and explore it with WebGL. No image is sent to an inference server. The official TRELLIS.2 experience is a clearly labelled external link, not an integrated generation service.

## Implemented

- Drag/drop or file selection; decode validation; 20 MB/80 MP limits; texture capped at 1600 px.
- Real AI inference with Transformers.js 3.8.1. WebGPU fp32 with WASM q8 fallback, progress, cancellation, timeout and retry. Lazy downloads only after Generate.
- Pinned model `onnx-community/depth-anything-v2-small`, revision `4472b7362082ad9968fee890ca0f1e5aca36b93d`. Model files/runtime WASM download from Hugging Face/jsDelivr; network access is needed initially. Browser caches may be evicted.
- Floating-point inverse depth is retained for mesh reconstruction (no intermediate 8-bit quantization), with perspective compensation. Adaptive grid diagonals follow the smaller depth jump. Surfaces stay connected by default to avoid black cracks; optional edge separation removes triangles crossing depth discontinuities to reduce stretched foreground texture. Neither mode invents background inpainting or back surfaces.
- Texture/depth/point cloud modes; depth strength/inversion; mesh resolution; bounded orbit, keyboard rotation, zoom; automatic subtle motion respecting reduced motion; fullscreen; original comparison.
- PNG render, grayscale depth PNG and self-contained textured binary glTF (GLB) export.
- Original analytic landscape demo, explicitly marked DEMO, loads without the model. It is not presented as AI output.
- Strength/inversion changes update existing position buffers; render-mode changes reuse geometry. Point-cloud attributes share mesh buffers. Rendering pauses when off-screen or hidden and static views render only on changes. Automatic motion waits until a drag has ended before starting its pause interval.

## Capability boundary

This is a single-view 2.5D depth relief, not a watertight 360° reconstruction, measured geometry, or a printable solid. Depth is relative, not metric. Large rotations expose unobserved surfaces. Complete object reconstruction by TRELLIS.2 needs a GPU service (official repo minimum 24 GB NVIDIA VRAM); GitHub Pages does not execute this service. Users can open the official demo voluntarily; photos are never automatically transferred there.

## Technical/design research (2026-09-19)

- [Microsoft TRELLIS.2](https://github.com/microsoft/TRELLIS.2): image-to-3D generation with O-Voxel and material synthesis; informs the optional full-object route.
- [Tencent Hunyuan3D 2.1](https://github.com/Tencent-Hunyuan/Hunyuan3D-2.1): full-asset generation and PBR material pipeline; also requires dedicated inference infrastructure.
- [Depth Anything V2](https://github.com/DepthAnything/Depth-Anything-V2), [ONNX model](https://huggingface.co/onnx-community/depth-anything-v2-small): the practical on-device implementation used here, not claimed to be the newest model overall.
- [Transformers.js WebGPU](https://huggingface.co/docs/transformers.js/guides/webgpu): device selection and browser inference.
- [Apple HIG Materials](https://developer.apple.com/design/human-interface-guidelines/materials): clear content/control hierarchy and readable translucent controls. Applied as a quiet solid sidebar, dominant dark canvas, and restrained floating controls. Original visual design, not a copy of an Apple screen.

## Dependencies and licenses

Three.js 0.180.0 (including OrbitControls and GLTFExporter), MIT; Transformers.js 3.8.1, Apache-2.0. Pinned browser distributions and their licenses are in `vendor/`. The model is Apache-2.0 and downloaded on demand. Source URLs use `https://cdn.jsdelivr.net/npm/three@0.180.0/` and `https://cdn.jsdelivr.net/npm/@huggingface/transformers@3.8.1/`. Do not put secrets in this static app.

Serve the repository root over HTTP, then open `/visuals/3d/`. WebGPU needs a secure context (HTTPS or localhost). WASM single-thread mode works without cross-origin isolation. No build step.

## Verification

Optimization revision: five Node regression tests cover floating-point depth, degenerate predictions, continuous/separated topology, triangle winding, perspective-preserving buffer updates and mocked GPU-to-WASM fallback. These tests do not execute the AI model or a browser. JavaScript syntax and local asset references checked; this revision has not repeated the browser tests below.

2026-09-19, isolated macOS Chrome: real photo completed both WebGPU fp32 and WASM q8 inference (the latter with WebGPU capability removed in the test worker). Cancel/retry and corrupt-image feedback passed. Desktop 1440 px / mobile 390 px layouts inspected, no horizontal overflow. PNG/depth PNG downloaded; binary GLB parsed with embedded texture and mesh, without a duplicative vertex-colour multiplier. Fullscreen entry/exit and point-cloud mode also verified in the in-app browser. These checks do not claim testing on physical Android/iOS devices.
