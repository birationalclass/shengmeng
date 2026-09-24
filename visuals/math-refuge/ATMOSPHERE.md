# Continuous Shanghai atmosphere

The scene uses Shanghai local time (UTC+8) and NOAA fractional-year solar coordinates. Sun direction, direct and ambient light, fog, water highlights, room lighting and the sky update continuously. Time preview approaches the selected hour along the shortest arc, including midnight.

The disk has a physical baseline radius and an artistic scale of 2 in ordinary daytime and up to 4.95 at sunrise (three times the previous sunrise disk), blending smoothly by elevation; sunset uses twice its previous size for wide-angle readability. It is not an astronomical angular-size simulation. The star-point and diffuse Milky Way rendering is described below. ESO/S. Brunier attribution and CC BY 4.0 remain linked in the time panel and assets/sky/CREDIT.md. A cached environment probe changes intensity continuously; it is not a live sky reflection map.

Open-Meteo supplies current weather at fixed Shanghai coordinates. No user geolocation is requested. Refresh: 15 minutes. Timeout: 10 seconds. Cached observations expire after two hours. Offline fallback is visibly labelled. Cloud cover, wind-driven cloud motion and fog blend over four seconds; rain preview and live precipitation drive up to 1,800 tapered, translucent instanced rain ribbons in one draw call. Roof footprints exclude indoor rain. Soft edges, varied lengths, distance fading and continuous world-space motion avoid screen-overlay rain; expanding impact rings perturb sea normals. Clear preview targets zero cloud and rain; cloud opacity vanishes continuously at zero coverage.

Water depth is an artistic continuous field in metres: western and southern shoals, an eastern channel and deeper open water. Beer–Lambert-style absorption blends sand/green shallows into blue depths. It is neither bathymetric survey data nor a navigational map.

Sources: https://gml.noaa.gov/grad/solcalc/solareqns.PDF and https://open-meteo.com/en/docs.

## Blackboard controls and tests

Writing speed and camera return delay live in the right-hand blackboard module. Erasers leave the board, turn outside the tray, move above it, and descend vertically; pickup reverses the path. Collision regression checks the board backing and every tray floor/lip.

stroke-test.html is a single-page proof of concept with authored centreline strokes, pen lifts, speed/seek controls and a formula-size slider (default 90%). The current preview compares the original authored strokes with refined, more compact cursive glyphs. Both use explicit pen contacts and lifts; automatic font skeleton ordering was rejected in visual review and removed from the selector. Production now defaults to the refined authored style. Blackboard settings can restore C · Marck Script (non-stroke reveal); the selection persists locally. Supported Latin letters, digits and operators follow explicit centreline contacts and pen lifts, shared by the ink reveal and chalk pose. Chinese and unsupported mathematical symbols retain their original glyphs and reveal method. Mathematical alphabets with distinct meanings remain unchanged. Nested SVG clipping and measured cover wrapping preserve layout bounds. The displayed performance numbers measure only 2D stroke drawing, excluding 3D rendering and texture uploads.

## Time panel

The top-right Time button owns all time/weather controls. Play/pause uses the selected 1×, 5×, 10×, 30× or 60× rate. The simulation wraps through midnight; real-time sync restores the Shanghai clock. Event buttons seek to three minutes before sunrise/sunset and start at the selected rate. Open-Meteo event times are preferred; local NOAA-derived horizon crossings supply an explicitly labelled fallback. These are time controls, independent of camera-tour speed.

Blackboards start in English; the existing touch control still switches to Chinese.

The far ocean fills the lower sky hemisphere and shares a pixel-antialiased horizon with the solar disk. Ocean fog is blended in linear light before the same output mapping as the sky.

Night-sky design references: https://github.com/sebh/UnrealEngineSkyAtmosphere (production atmosphere separation and radiometric principles), https://ebruneton.github.io/precomputed_atmospheric_scattering/ (scattering reference), and https://stellarium.org/files/guide.pdf (altitude-dependent extinction/scintillation). This implementation is an artistic lightweight approximation, not a port of their full scattering LUTs or a calibrated star catalogue.


## Sky revision 75

The previous noon horizon was a fixed pale RGB gradient, combined with a pale ocean/fog fallback. The new sky-view LUT integrates single scattering through a spherical atmosphere: altitude-dependent Rayleigh and Mie densities, ozone absorption, Beer–Lambert extinction along the view and solar rays, and planetary shadowing. The 256 × 128 half-float LUT concentrates elevation samples near the horizon and updates with sun direction and cloud-dependent aerosol loading. Final sky display is tone-mapped once. Clear mode uses lower aerosol loading and much lower near-field fog density; the distant ocean fallback is blue rather than pale white.

References consulted: Eric Bruneton's [precomputed atmospheric scattering](https://ebruneton.github.io/precomputed_atmospheric_scattering/) and Sébastien Hillaire's [2020 sky/atmosphere technique](https://sebh.github.io/publications/). This is a compact single-scattering adaptation, not a full implementation of their multiple-scattering, ground-irradiance or aerial-perspective LUT systems. Weather and cloud rendering remain artistic; this is not a calibrated atmospheric instrument.

Individual stars are no longer enlarged photographic highlights. A median-filtered ESO panorama supplies diffuse galactic light only; deterministic celestial point sources have pixel-sized Gaussian footprints, subdued warm/cool tint, brightness variation and low-amplitude scintillation. The distribution is artistic, not a star catalogue. Celestial coordinates remain continuous as time advances. Weather clouds still cover both layers.


## Wind-driven volumetric clouds (77)

The old 2D sky-noise cloud overlay is removed. A periodic 64³ density texture combines multi-scale value noise with Worley cells; a 1.3–3.1 km spherical cloud layer is ray-marched using 32 view samples and two lower-detail solar-shadow samples. Density erosion, a vertical profile, Beer–Lambert extinction and forward scattering supply edges, dark bases and lit rims. All visible clouds share this 3D volume and cover the sun, stars and galaxy. A 1024×512 premultiplied angular buffer is regenerated at up to 10 Hz, with continuous interpolation between two buffers; sampling is denser near the horizon. Deterministic ray offsets reduce marching bands without frame-random sparkle. This is a bounded WebGL adaptation of volumetric-cloud principles, not a full Nubis implementation or a weather-resolving fluid simulation.

Open-Meteo now requests wind_direction_10m as well as wind_speed_10m. Bearing is the meteorological source direction: north wind moves toward scene +Z (south), east wind toward -X. Speed is converted from km/h to km/s and integrated into persistent cloud position; updates blend velocity vectors over four seconds, including 359°→1°. Missing direction is displayed as unavailable; the renderer retains its last direction or initial preset. Cache v2 avoids treating old entries as wind-bearing observations. Clear/cloud/rain previews retain observed wind. Time playback scales advection up to the existing 60× setting; paused clock previews keep ordinary wind motion.

The measured 10 m wind is explicitly a cloud-advection proxy, not measured wind at cloud altitude. The layout and shape of individual clouds are procedural, not a reconstruction of actual Shanghai cloud locations. References: https://open-meteo.com/en/docs and https://www.guerrilla-games.com/read/nubis-realtime-volumetric-cloudscapes-in-a-nutshell .

## Inhabited-island shallows
Campus decks and the remote residence have independent 1.5–3 m artistic shelves. Plan-coordinate distance fields blend into 88 m offshore depth over approximately 260 m; the intervening channel remains deep. Residence shelf coordinates derive from its layout. Existing water absorption converts depth continuously to water colour. These values are visual design, not surveyed bathymetry.

## Display controls, September 25
The settings panel groups display/performance, environment, and input/audio. Reference-video links and production commentary were removed. Blackboard-specific clarity remains in the blackboard panel. Preferences persist locally. Device capability and GPU identification choose an initial configuration; disjoint-safe GPU timings adapt cloud quality and resolution. Mobile defaults to standard clouds, simple sky reflections and no star field. RTX-class desktop defaults to 125% rendering, 2048 shadows, 16x texture filtering and medium clouds, targeting a 60 Hz GPU budget (not a frame cap). No DLSS/FSR is claimed.

The cloud tiers use 256×128/16 steps, 512×256/24 steps, and 1024×512/32 steps, refreshed at minimum intervals of 400/250/160 ms and split over tiles. Clear skies skip empty cloud passes. A settings-only GPU query samples atmosphere/cloud precomputation separately from the full-frame query; these queries never nest. This is not the GPU cost of the complete weather system: sky/water/rain draw in the main scene. No extension means no fabricated GPU result or frame-rate-based GPU degradation.

RTX 3080 Ti, browser viewport 1280×720, 125% resolution, fixed terrace camera (65.056,2.121,4.241), noon/cloudy: medium vs high cloud samples gave frame P95 7.0 vs 7.1 ms, CPU P95 1.8 vs 2.1 ms. Prepass sampled means were approximately 0.005 vs 0.019 ms before the final de-correlated query cadence; these tiny, intermittent-pass samples are not an overall weather cost estimate or a cross-machine benchmark. The GPU is not saturated in this view. Hardware readout also identified an i9-12900KF. Main-scene work, viewport size and visible classrooms change these results.

Reading protection keeps selected resolution while inside a visible classroom. Blackboard textures retain trilinear mipmaps and up to 16x anisotropy; a modest -0.45 mip bias preserves fine ink without disabling mipmaps. A natural-filter option restores zero bias. Subpixel handwriting cannot be made legible at arbitrary distance; the existing high-resolution reader is retained.

Ocean colour now samples the current atmosphere/cloud panorama, uses Schlick water Fresnel and a bounded GGX sun lobe, and gates direct reflection as the visible disk crosses the horizon. Water aerial perspective and the sky below the horizon share grazing sky radiance instead of a fixed blue fog strip. This remains a compact approximation without traced building reflections or a multiple-scattering ocean volume.

Wind advects water normals using integrated weather-wind offsets. Wind speed controls slope amplitude/roughness; meteorological FROM direction is converted to travel direction with the same continuous vector used by clouds. Controls expose wind-driven waves, amplitude, reflection detail and direct solar reflection. The Shanghai 10 m wind is a visual proxy, not an ocean wave forecast. Wheel input now translates camera and target together without changing FOV.

References: [Guerrilla Nubis³](https://www.guerrilla-games.com/read/nubis-cubed), [NVIDIA dynamic-resolution guidance](https://github.com/NVIDIA/DLSS/blob/main/doc/DLSS_Programming_Guide_Release.pdf), [Epic water shading](https://dev.epicgames.com/documentation/unreal-engine/single-layer-water-shading-model?application_version=4.27), [Three.js texture filtering](https://threejs.org/docs/pages/Texture.html). Techniques are adapted to this WebGL scene, not implementations of those proprietary engines.


## Environment follow-up (v86)
Time/weather/night controls now live in the settings accordion; the clock is a shortcut. Natural and vivid diffuse-galaxy exposure share the same texture and sample count. This is an artistic orientation/exposure, not a date-calibrated planetarium. Meteors use a great-circle tangent basis, tapered analytic trail and Gaussian head; angular pixel derivatives are computed before branching. Water uses its own real-time wind integrator and swell phase, never the scene-time multiplier. Clouds and celestial rotation follow scene time. Sun reflection uses smooth bounded radiance instead of a hard 12-unit clamp; this is an artistic energy bound, not a calibrated ocean BRDF.
Near-horizon solar rays use standard-atmosphere refraction (Bennett approximation), without inversion-layer mirages. Hall floor camera transitions route via the exterior stair; manual motion clips the floor slab. Shadow footprint tightens near the hall; structural dark floor edges remain materials rather than projected shadows.
