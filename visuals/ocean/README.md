# 潮汐之间 · Between tides

A real-time coastal seascape for Visual Lab, built in WebGL 2 using the repository's vendored Three.js r180. No remote runtime dependencies or downloaded ocean footage.

## Model

- **Offshore:** an independently implemented Pierson–Moskowitz energy spectrum drives 32 directional Gerstner components, with gravity-wave dispersion at a reference depth of 8 m. Frequencies and phases stay fixed when wind changes; wind redistributes energy. Amplitude is normalized for the visual control. The primary surf travels at 2.05 m/s. Short components fade with distance to limit undersampling.
- **Nearshore:** original cubic cross-sections blend with lower spilling profiles. Wave groups vary in strength and arrival; shoal variation makes different sections break at different times. Displacement fades out through collapse and approaches zero near the shoreline, keeping water and sand coordinates aligned.
- **Whitewater:** 768 × 768 half-float render targets transport and dissipate foam. Half-float storage avoids the high-frame-rate decay freeze of the former RGBA8 field. A separate displaced mesh adds density-dependent thickness, rounded clumps and directional shading; fresh breakers pile up and residual foam thins. A depth-correct spherical-impostor layer adds small froth clusters near the viewer, with filtered microbubble normals on the surface. It is a surface approximation, not a volumetric gas/liquid simulation. Ballistic particles represent light spray.
- **Swash and wet sand:** a continuous wave-linked runup profile advances and recedes. Water depth and coverage taper smoothly, with sand showing through the thin film. The second simulation channel stores wetness, drying over a longer period than foam. Wet-sand reflections persist after the water retreats.
- **Lighting:** procedural sky/cloud reflections, Fresnel reflection, band-limited capillary detail, directional specular and approximate transmission.

This is an artistic hybrid, not a FLIP/Navier–Stokes solver, an FFT ocean, or an engineering prediction. Wave height is a visual scale, not measured significant wave height. The model uses an authored surf train with spatial and wave-group variation. WebGL 2 and `EXT_color_buffer_float` are required.

## Controls

Drag to look around; scroll to change eye height. Choose golden hour, clear day or dusk. Adjust wave scale, wind detail, sun elevation and playback speed. Space pauses; H hides controls; F opens fullscreen. While paused, the advance button moves the model forward half a second, including foam transport. Sound is opt-in; hidden tabs stop animation and mute sound. Reduced-motion users start paused.

## Checks

```sh
node --check visuals/ocean/ocean.js
node --check visuals/ocean/ocean-renderer.js
node visuals/ocean/model-check.mjs
```

The Node check validates the base authored profiles, not the full composed water surface. For the composed shader, serve and open `geometry-check.html`: it reads actual GPU outputs over 24 seconds, 3 wave scales and 5,922,816 samples. It checks finite positions, shore-coordinate alignment, continuous runup motion and positive bounded foam thickness. Browser QA additionally covers the full breaking cycle, wet/dry transitions, presets, sliders, pause/step, view drag, mobile layout and both mesh-quality settings. These are numerical and functional checks, not a claim of photorealism.

## Research and attribution

- [Hugh Malan / Guerrilla, Rendering Water in Horizon Forbidden West, SIGGRAPH 2022](https://advances.realtimerendering.com/s2022/SIGGRAPH2022-Advances-Water-Malan.pdf): animated wave cross-section deformation and wavefront control. Our curves, mesh, shaders and code are independently authored; no game assets or baked simulation data are used.
- [NVIDIA GPU Gems, Effective Water Simulation from Physical Models](https://developer.nvidia.com/gpugems/gpugems/part-i-natural-effects/chapter-1-effective-water-simulation-physical-models): directional Gerstner waves and multiple scales of surface detail.
- [SideFX Houdini, Oceans](https://www.sidefx.com/docs/houdini/fluid/oceans.html): separating ocean shape, whitewater and surface lighting.
- User-supplied sunset shore photos informed composition and color only; they are not bundled.
- [miaoziemm/Ocean-wave-simulation](https://github.com/miaoziemm/Ocean-wave-simulation) was reviewed for its PM-spectrum and directional-wave ideas. No MATLAB source was copied; its incomplete SPH examples are not used. A spectrum alone does not model shoreline wetting/drying or breaking-wave foam volume.
- Three.js remains under its MIT license in `../3d/vendor/`.

`cover.jpg` is a capture of this renderer, not a stock or AI-generated image.
