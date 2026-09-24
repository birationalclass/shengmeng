# 潮汐之间 · Between tides

A real-time coastal seascape for Visual Lab, built in WebGL 2 using the repository's vendored Three.js r180. No remote runtime dependencies or downloaded ocean footage.

## Model

- **Offshore:** 18 deterministic directional Gerstner components, with gravity-wave dispersion at a reference depth of 8 m. The primary surf travels at 2.35 m/s in irregular fronts.
- **Nearshore:** original, authored cubic wave cross-sections interpolate through rising, steepening, curling and collapse. A 512 × 160 half-float deformation texture drives a coast-aligned mesh, including the underside of the lip. This supports actual overhangs, which a single-valued height field cannot represent.
- **Whitewater:** a pair of 768 × 768 RGBA8 render targets stores foam, advects it toward the shore and dissipates it over time. Curling/breaking regions continuously inject new foam. A separate ballistic particle layer represents spray.
- **Lighting:** procedural sky and clouds, Fresnel reflection, directional specular and approximate transmission. Sand and water use the same coast coordinates.

This is an artistic hybrid, not a FLIP/Navier–Stokes solver, an FFT ocean, or an engineering prediction. Wave height is a visual scale, not measured significant wave height. The model uses a authored repeating surf train, with spatial variation and an independent directional wave field.

## Controls

Drag to look around; scroll to change eye height. Choose golden hour, clear day or dusk. Adjust wave scale, wind detail, sun elevation and playback speed. Space pauses; H hides controls; F opens fullscreen. While paused, the advance button moves the model forward half a second, including foam transport. Sound is opt-in; hidden tabs stop animation and mute sound. Reduced-motion users start paused.

## Checks

```sh
node --check visuals/ocean/ocean.js
node --check visuals/ocean/ocean-renderer.js
node visuals/ocean/model-check.mjs
```

The geometry check samples all 160 profile stages, verifies finite values, flat periodic boundaries and real overhangs, and checks sampled cross-sections for self-intersections. Browser QA must additionally cover the full breaking cycle, presets, sliders, pause/step, view drag, fullscreen, mobile layout, capture, hidden-tab behavior and graphics fallback.

## Research and attribution

- [Hugh Malan / Guerrilla, Rendering Water in Horizon Forbidden West, SIGGRAPH 2022](https://advances.realtimerendering.com/s2022/SIGGRAPH2022-Advances-Water-Malan.pdf): animated wave cross-section deformation and wavefront control. Our curves, mesh, shaders and code are independently authored; no game assets or baked simulation data are used.
- [NVIDIA GPU Gems, Effective Water Simulation from Physical Models](https://developer.nvidia.com/gpugems/gpugems/part-i-natural-effects/chapter-1-effective-water-simulation-physical-models): directional Gerstner waves and multiple scales of surface detail.
- [SideFX Houdini, Oceans](https://www.sidefx.com/docs/houdini/fluid/oceans.html): separating ocean shape, whitewater and surface lighting.
- User-supplied sunset shore photos informed composition and color only; they are not bundled.
- Three.js remains under its MIT license in `../3d/vendor/`.

`cover.jpg` is a capture of this renderer, not a stock or AI-generated image.
