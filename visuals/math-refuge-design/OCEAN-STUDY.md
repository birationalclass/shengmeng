# Current coast: experiment 01 (2026-09-25)

The campus now embeds `../ocean/elliptic-renderer.js` directly with the existing
renderer and camera. Both sand ribbons, the kilometre distance field, 02 optical
water, shallow overtopping, gentle ±10 cm relief, slow submerged branch tips,
projected wave filtering and distant ocean depth are shared with 01. The former
campus sand shelf and the four decorative offshore islands are no longer drawn.
The campus keeps its real-time sky, cloud reflection, weather and solar direction.
Geographic east is mathematical +x and north is +y. The coast overview is north-up;
world +X is east and world −Z is north. The coast is translated only, with no
90° rotation. Solar and cloud directions keep their original geographic frame.
The main auditorium starts with all six boards fully stowed, without a startup
lowering animation; the storage control or report selection can raise them.

`elliptic-site.js` defines a rigid metre-scale embedding: the main auditorium
centre maps exactly to mathematical `(x,y)=(2,0)` km. The architectural campus
retains its connected platforms west of the coastal auditorium; room/furniture dimensions and teaching camera routes
stay intact. Garden and guest terraces can extend over shallow water; continuous
platform fascia now reaches below the sand. The detached residence follows the
same branch 1.25 km south of the apex, with its interior viewpoints and
room bounds translated together. Sailboats and kayaks moor beyond the sand and
follow the current tide vertically. Buildings remain above peak demo tide.

Navigation adds **曲线海岸总览**, **左环漫滩**, **主楼沙滩**. Settings expose 250 m
grid lines, base tide, tidal animation and wave pause. The orbit range now covers
14 km. Coast coordinates display the original equation's y axis, opposite Three's
local z. The existing indoor navigation and board interactions remain available.
All quality modes retain this terrain and water model. Lower tiers reduce short
normal bands and fine spray; larger breaking bands retain their independent LOD.
There are no extra WebGL contexts or old foam ping-pong render targets.

Validation: numerical placement/inverse transform, shared terrain samples,
residence viewpoints and water clearance, plus existing hall-route and villa-plan
tests (42 scene checks and 12 placement/navigation/plan checks pass). Local browser checks cover full coast, main campus, settings and shader
compilation. No GitHub publication is implied by these local checks.

---
The following is the implementation history, superseded by the shared 01 above.

# Ocean Study integration

The campus imports `createOceanLayer` from `../ocean/ocean-renderer.js`; it does not duplicate or approximate the original wave solver. The original page still creates its own renderer, sky and camera. The embedded layer shares the campus renderer, camera and render loop.

Reused unchanged: the 32-component wave spectrum, authored overturning profiles, 30 Hz ping-pong foam transport, retained wetness, raised whitewater sheet, froth and spray. `ocean-study.js` adapts geographic coordinates, samples the existing campus bathymetry for shoreline/bed height, uses campus sky/cloud textures and sun direction, and replaces colour transfer with the host's tone mapping and depth-dependent transmission. The existing granular sand material reads the original foam buffer's wetness channel. Offshore water remains the existing campus material and blends through the shallow shelf.

Settings → Environment offers Ocean Study / previous sea and an independent surf sound switch. Sound uses the original filtered brown-noise synthesis, a smoothed distance gain `0.32 / (1 + (distance / 24)^1.65)`, and distance-dependent low-pass filtering. Distance includes observer height and is measured to sampled shore points. Audio begins only after enabling the switch and mutes when the page is hidden. It is procedural audio, not a recorded beach or acoustic obstruction simulation.

This is the original artistic real-time model, not a FLIP simulation. The east-facing study patch fits the current campus shelf; it does not turn every remote island into a breaking beach. Fine study geometry adds about 1.08 million triangles; standard water detail uses the original reduced mesh sizes. The architecture keeps its existing independent 1.3 million triangle budget.

The separate `../ocean/shorelines.html` experiment draws three idealized shoreline types with independent tide/time settings: a Nang Yuan inspired triple sandbar, crescent bay, and Zlatni Rat inspired gravel spit. It reuses the ocean spectrum but uses a distance-field shoreline model for these different topologies; it is a morphology experiment, not the original overturning-wave model or surveyed geography. The existing four local experiments remain intact.

Validation: 111 campus tests pass, including bathymetry, geographic placement, audio attenuation and scene assembly. Browser checks cover shader compilation, both water models, standard geometry, sound activation, three shoreline selectors and top-down view. No perceptual match to offline FLIP footage is claimed.

## Measured adaptive sea (2026-09-25)

The default is now **Auto**, initially a lightweight continuous sea. Two-second foreground frame windows measure mean FPS and P95 even without GPU timer support. Two poor windows reduce quality; severe slowdown drops directly to lightweight. Sixteen healthy seconds permit one upward trial, with GPU headroom checked when available. A failed tier waits at least 60 seconds before retrying, increasing to five minutes after repeated failures. A 120 FPS preference is bounded by observed browser cadence rather than treating a 60 Hz browser as permanently failing. Manual lightweight, standard and Ocean selections remain available. Old saved default Ocean selections migrate to Auto once; subsequent explicit choices persist.

Lightweight water keeps the coast, depth, day/night sky colour, moving normal ripples and solar highlights, but skips the inverse shore-surface search, multi-layer normal sampling, ripple Hessians, caustics and surf transport. Standard uses the existing campus shader; Ocean adds the original breaking surf. Ocean geometry and foam targets are allocated only on first enable, then reused. Disabled updates perform no foam simulation, and restart from current water time without the original 96-pass prewarm or catch-up. Automatic mode pauses the study while inside teaching rooms and continues to show the surrounding sea. No campus architecture, boats or shore geometry is removed.

Validation: 115 campus tests passed, including GPU-query-free adaptation, recovery cooldown, background reset, room eligibility and 60/120 Hz cadence. The 42 scene checks were rerun with lazy allocation and disable/re-enable assertions. At the same sea-terrace camera in the local M4 Codex Chromium browser, forced Ocean recorded frame P50/P95 51.0/66.9 ms (render scale 0.65, 1,363,916 triangles); Auto lightweight recorded 16.7/17.6 ms and 60 FPS (scale 0.79, 288,716 triangles). These are rolling observations under adaptive resolution, not a controlled GPU benchmark or Safari measurement. Both shaders compiled without console errors and screenshots showed intact sea, shore and boats. Stable 60 FPS is a target, not a guarantee for every view or machine.
