# 01 · Elliptic beach ribbons

Entry: `experiments.html#original` → `elliptic-beach.html`.
The existing hash remains compatible with links from the visual laboratory.
The previous single-coast page remains at `index.html`; 02 is still independent.

## Geometry and scale

The centreline satisfies y² = x(x−1)(x−2), with one equation unit = 1 km.
World coordinates are metres; mathematical y maps to negative world z.
Only the 50 m neighbourhood on either side of the curve is sand.
The closed component's interior, the gap, and the open component's interior
are water. The sand slopes towards water on both sides at approximately 5.5%,
inherited from 02. The crest is rounded over 2 m; the seabed is capped at −18 m.

`bake-elliptic-field.py` builds a nearest-polyline distance field (4096²,
4 m texels, centimetre encoding). The field is linear-filtered without mipmaps
or colour conversion. Explicit ribbon meshes preserve the narrow shore at
kilometre viewing distances; an adaptive water mesh concentrates detail near
the observer. The finite open branch extends beyond the initial overview.

## Shared 02 optics

01 imports all five optical GLSL exports from `coastal-optics.js`: sand albedo
and illumination, refracted bed intersection and spectral absorption,
filtered capillary normals, Fresnel transmission/reflection, GGX/Smith sunlight,
and reflective wet sand. It also shares 02's sky, tone mapping, and wave spectrum.
`CURVED_COAST` supplies world-space coordinates, numerical bed slopes, and bed
normals for the refracted-ray solve. The default path used by 02 keeps its
existing straight-coast equations.

This transfers the new **optical material**, not the single-coast curling-wave
geometry or its rectangular foam-history simulation. 01 uses spectral surface
waves and shallow-water foam on both sides of the ribbon. It is not a fluid
solver and does not model diffraction or wave transmission across dry sand.

## Interaction and checks

Human eye height initially: 1.7 m above sand, 46 m from the centreline towards
the selected water side (about 4 m before the shore). Ring position,
inward/outward views, right branch, aerial orbit,
plan grid, daylight/sunset/dusk, wave height, pause and reset are available.
The minimap has 0.5 km squares; the plan-view surface grid has 0.25 km squares.
Inactive iframes and hidden documents stop advancing. View and controls persist
when switching experiment tabs during the same page visit.

Human-view movement is independent of look direction: WASD/arrows move on the
horizontal plane, Q/E lower/raise eye height, Shift accelerates, the wheel moves
forward/back, left drag looks through 360° yaw and ±88° pitch, and right drag
translates on the horizontal plane. The on-screen controls step 10 m per click
or move continuously while held. Movement remains active with waves paused.
Ground height is sampled from the same distance texture as the water material;
the camera stays above sand or sea level. Moving over the water is an observer
mode, not a swimming simulation. Blur/visibility changes clear held inputs.

Validated in the local browser: shaders compile, human and grid views,
ring-position and lighting controls, pause, 01/02 switching with identical
paused time retained, and 02's existing shader path. Numerical samples check
water in both component interiors, dry sand at both centrelines and offsets,
and the two 50 m shoreline offsets. JavaScript syntax and whitespace checks
also pass. The depth range changes for aerial views to avoid seabed z-fighting.

## Shallow overtopping

The default tide oscillates around +2.55 m with a 0.28 m amplitude and a
40-second demonstration period (not a real-world tidal timescale). The crest
is about +2.64 m with up to ±0.10 m of gentle relief, so the mean surface at high tide covers it by about 9–29 cm;
small waves add local run-up. Low tide exposes the crest again. A base-level
slider and a tide toggle allow same-frame comparisons while waves are paused.

The same tide uniform drives water displacement, local depth, shoaling, foam,
refraction thickness and sand wetness. Free-observer camera height follows
sufficiently deep water to keep the eye above the surface. The new default
`wash` view starts on the crest looking along the sand ribbon.

Checked: high-water coverage versus exposed crest at a +2.25 m fixed tide,
paused tide adjustment, shared optical shader compilation, and the 40-second
period and high-tide overtopping numerically.

## Gentle sand relief

Two stationary, low-frequency sine bands add at most ±10 cm of height,
with wavelengths of roughly 124 and 236 metres. Relief fades smoothly across
the submerged skirts (40–140 m from the centreline). The CPU mesh and walking
height use the same formula as GLSL bed normals, optical depth and wave run-up.
The −18 m floor and gradual right-branch descent remain in place. The tide
indicator describes partial/full overtopping instead of assuming a flat crest.

## Right-branch submerged ends

Both arms keep the elliptic centreline and their 100 m cross-section. Starting
1.8 km north/south of the apex, a squared smoothstep vertical offset gradually lowers the
ribbon, reaching the common −18 m floor near 7.3 km before its mesh ends. The squared profile keeps the first part almost level; at zero tide the crest enters the sea around 3.9 km from the apex. The dry ribbon
narrows naturally at the waterline, then remains visible through shallow water
and fades with optical depth. This is geometric descent, not opacity fading.
The closed ring is unchanged. Mesh heights, GLSL bed intersections and CPU
camera ground sampling share this profile. The distance texture now spans
16.384 km with the same 4 m texels, covering the entire submerged ribbon.

Validated the descent's monotonicity and north/south symmetry, unchanged ring,
field coverage including skirts, −18 m end heights, and the low-tide aerial
transition in the browser.

## Panoramic horizon

Adapted the horizon treatment in Math Refuge (`scene.js`, `weather-sky.js`):
the below-horizon sky and distant water use identical grazing sky radiance,
with a slight water tint retaining the sea/sky distinction. 01 retains its
adaptive wave mesh and shared 02 near-water optics. A radial transition from
6.5 to 9.5 km completes before the 10 km square mesh boundary, hiding its
corners at all headings. This is a panoramic flat-ocean horizon, not a
curved-Earth simulation or a circular beach/sea boundary.

## High-view rendering and foam LOD

Fine foam fades with projected pixel footprint, 60–180 m view distance and
25–80 m height above the current tide. Larger breaking-wave bands remain at
full height visibility through 180 m, fading gradually to 650 m; their phase
footprint also filters unresolved bands. Only at 680 m does the renderer switch
to `FOAM_DETAIL=0`, returning below 650 m with a zero-weight transition.
At 80 m the fine foam is gone, but the larger moving bands remain. Short gravity
waves omitted from the geometric mesh now contribute animated fragment normals,
filtered by projected wavelength rather than a camera-height cutoff. This keeps
metre-scale wave reflections visible after tiny capillary detail fades.
Near-water optical functions remain shared with 02; no speedup percentage is claimed.

High views now use a ray/plane distant ocean that writes water depth beyond
9 km and continues the near ocean's Fresnel, sky reflections and GGX sun.
This replaces the visible solid-colour strip and prevents submerged sand from
showing through beyond the finite detail mesh. Camera clipping ranges follow
height. Distant submerged sand fragments are omitted because the water shader
already reconstructs their bed, preventing high-view depth fighting.

Verified both foam shader variants, smooth fade/hysteresis numerically, and
near/aerial/distant views in the browser, including approximately 9 km height.
