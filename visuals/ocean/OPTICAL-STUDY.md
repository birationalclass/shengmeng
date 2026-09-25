# Coastal optics experiment

Open `optical-study.html` using the local static server. The normal ocean page
continues to use the original material. Pause and switch between the two buttons
to compare exactly the same geometry, camera, foam history and simulation time.

The experimental shader shares the sand albedo between exposed beach and seabed,
intersects a refracted view ray with the existing sloping beach, and applies
per-channel exponential extinction to that path. It combines this transmission
with Fresnel reflection, a GGX/Smith sunlight term, and pixel-filtered short-wave
normals. This is an approximation: no multiple scattering, scene-object
reflections, caustic solver, or true subsurface wave-volume intersection.

The original curling geometry, prescribed swash and foam transport are unchanged.
This experiment cannot establish the realism of breaking surf. In visual review,
the optical differences are visible, but long crest bands, repeated wave shapes
and foam clumps remain prominent. Those require a separate geometry/motion study.

Validation: JavaScript syntax, browser shader compilation, same-time A/B switching,
sunset/day/dusk controls, pause/resume, 390×844 responsive view, and existing
authored-profile finite/seam/self-intersection check. No mobile hardware performance
claim is made from a resized desktop viewport. No publication performed.

Reference principles (independent implementation, no UE source/assets copied):
- https://dev.epicgames.com/documentation/zh-cn/unreal-engine/single-layer-water-shading-model-in-unreal-engine
- https://dev.epicgames.com/documentation/zh-cn/unreal-engine/simulating-waves-using-the-water-waves-asset-in-unreal-engine
