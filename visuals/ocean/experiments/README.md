# Independent 3D beach-tank experiments

Open `../experiments.html`. The four tabs retain their own iframe, controls,
camera and playback time while switching. Inactive experiments stop advancing.
This retention lasts for the open page, not across a page reload. Original ocean
and optical-study defaults are not replaced by either fluid experiment.

## What was reproduced

Reference: https://www.bilibili.com/video/BV1qsT7zyEha/
Original linked in its description: https://www.youtube.com/watch?v=ok1ViHVcXYs

At approximately 1:46, the video visibly shows FLIP Fluids whitewater settings,
including Foam, Bubbles and Spray. Our experiments independently reproduce a
related pipeline: a moving paddle pushes a three-dimensional liquid volume onto
a sloping collision bed; the solver generates liquid surfaces and secondary
particles; the browser plays those changing-topology meshes and particles.

**This uses Blender 4.5.9's built-in Mantaflow FLIP/PIC, not the FLIP Fluids
addon shown in the tutorial. No tutorial project, commercial addon, rendered
footage or third-party animation assets were copied. It is not a photoreal match.**

## Preserved variants

| Cache | Grid resolution (longest axis) | Paddle stroke / period | Simulation | Playback |
|---|---:|---|---|---|
| beach-cache | 80 | 0.62 m / 2.1 s | 144 frames at 24 fps | 72 meshes at 12 fps |
| breaker-cache | 96 | 1.5 m / 2.8 s | 192 frames at 24 fps | 96 meshes at 12 fps |

Both use a 12 × 5 × 4.5 m domain, gravity 9.81 m/s², a 0.19 bed slope,
FLIP ratio 0.95, mesh upsampling 2, and 2–6 solver substeps. Browser positions
are quantized to 1 mm. Each gzip frame stores its own triangle connectivity;
this is not a fixed-topology morph animation. Nearby foam is projected to the
reconstructed free surface so it does not disappear inside the smoothed mesh.
Exported secondary particles are deterministically thinned to at most 12,000.

The first tank is too gentle to demonstrate convincing breakers. The stronger
tank exhibits more irregular crests, but limited resolution, closed side walls,
short duration, startup transients and simple rendering remain evident. It must
not be presented as a finished replacement for the ocean scene. Playback stops
at the end instead of pretending the simulation has a seamless loop.

## Rebuild

Run `bake_beach.py` with Blender in background mode. Set `OCEAN_BAKE_WORK` to a
scratch directory outside the published site; `OCEAN_VARIANT` controls the output
cache directory name. Other environment variables: `OCEAN_RESOLUTION`,
`OCEAN_FRAMES`, `OCEAN_PADDLE_STROKE`, `OCEAN_PADDLE_PERIOD`.

For export-only work set `OCEAN_EXPORT_ONLY=1` and the matching work directory,
resolution, frame count and variant. This opens the saved scene directly without
recreating a domain (which could invalidate the existing simulation cache).

Native scenes are in the workspace's `ocean-qa/mantaflow-beach`
and `ocean-qa/mantaflow-breaker`. Bulky intermediate solver caches were removed
after export validation to recover disk space; rebake before exporting again.
Official portable Blender, verified against its
official SHA256 file, is under `.tools/ocean-blender` in the parent workspace.

## Checks performed

- Validated all 168 compressed frames: lengths, vertex/index counts, valid index
  ranges, finite particle positions, and non-placeholder meshes.
- Weak cache: 18.91 MiB, 19,088–20,968 vertices/frame, at most 11,566 particles.
- Strong cache: 39.78 MiB, 25,606–38,248 vertices/frame, at most 11,955 particles.
- Browser playback and timeline scrubbing; four-way switching; paused time at
  3.75 s retained while optical experiment independently retained daylight.
- Desktop and 390 × 844 layout; responsive view is not mobile GPU benchmarking.
- JavaScript syntax and Git whitespace checks. Included in the complete Ocean Lab publication.
