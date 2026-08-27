# Parametric finite-element geometric-flow gallery

This WebGL page contains three numerical models from `sp电子科大.pdf`:

- the linear BGN parametric finite-element method for surface diffusion;
- the linearly implicit relaxed-MDR method for Willmore flow from Zhao,
  arXiv:2608.07244, equations (4.8) and (5.1);
- the area- and volume-constrained relaxed-MDR Helfrich method from equation
  (5.7) and Example 7.

The browser does not morph between hand-authored shapes. It reads saved nodal
states on one fixed triangulation and only interpolates between consecutive
computed time levels for smooth display.

## BGN surface diffusion

On the old surface `S^m`, `tools/generate_bgn_trajectory.py` solves

```text
< ((X^(m+1)-X^m)/tau) . n^m, phi >_h
    - < grad_S H^(m+1), grad_S phi > = 0,

< H^(m+1) n^m, eta >_h
    + < grad_S X^(m+1), grad_S eta > = 0.
```

The generator uses continuous piecewise-linear surface elements, a cotangent
stiffness matrix, and triangle-wise mass-lumped normal coupling. It checks
surface-area decay, the discrete energy defect, volume drift, topology, and
triangle nondegeneracy.

## Genus-two Willmore example

`tools/generate_willmore_trajectory.py` implements the closed-surface,
zero-spontaneous-curvature specialization of the paper's symmetric mixed
system. The initial surface is exactly the boundary of a `7 x 4 x 1` cuboid
after removing two `2 x 2 x 1` square through-holes. Parameters match the
lecture example: `alpha = 10`, `tau = 1e-3`, and `T = 5`. Connectivity remains
fixed, so the two holes and genus two are preserved.

The UI holds the square initial state for 1.8 seconds before advancing, then
plays the full evolution over 16 seconds. The generated trajectory saves every
five solver steps (1001 numerical states over `T = 5`), and the renderer
interpolates continuously between adjacent states. The timeline remains
directly scrubbable.

## Biconcave Helfrich example

`tools/generate_helfrich_trajectory.py` implements the PDF page 41 example:
a `4 x 4 x 1` oblate ellipsoid with zero spontaneous curvature evolves under
the area- and volume-constrained Helfrich flow. Two global Lagrange
multipliers impose the discrete area- and volume-velocity constraints, so the
surface cannot merely shrink or expand toward a sphere and instead develops a
biconcave equilibrium. Parameters are `alpha = 10`, `tau = 1e-3`, and
`T = 0.2`.

The downloadable web trajectory uses 572 vertices and 1,140 triangles. The
generator also supports the paper's exact mesh counts with `--latitudes 33
--longitudes 80`, producing 2,562 vertices and 5,120 triangles.

## Mesh refinement

The **triangle 1→4** option is an exact display subdivision of the original
PFEM trajectory. `tools/refine_trajectory.py` inserts one shared midpoint on
every original edge and replaces every triangle by four triangles at every
saved state. The refined mesh covers the identical piecewise-linear surface;
it does not invent a new trajectory or change energy, area, volume, or time.

## Regeneration

With NumPy and SciPy installed:

```bash
python3 tools/generate_bgn_trajectory.py --case all
python3 tools/generate_willmore_trajectory.py --steps 5000 --save-every 5
python3 tools/generate_helfrich_trajectory.py --steps 200 --save-every 1
python3 tools/refine_trajectory.py trajectories/genus-two.bin trajectories/genus-two-fine.bin --frame-stride 2
```

Run the refinement command analogously for `cube`, `torus`, and `oblate`.
`trajectories/manifest.json` maps each case to its original and 1→4 variants.
The genus-two original keeps all 1,001 saved states; its 1→4 download keeps
every second saved state (501 states) and relies on the same continuous display
interpolation, keeping the browser payload below the static-host upload limit.

## Honest scope

The original BGN scheme does not preserve volume exactly; the page reports its
measured drift. Unconstrained Willmore flow is scale invariant and also does
not preserve volume, so its relative volume change is shown rather than
treated as an error. The fully discrete Willmore scheme has a proved unique
linear solve, while the paper does not claim an unconditional fully discrete
energy theorem; the checked trajectory reports the observed monotone decay.
The Helfrich constraints make the discrete area and volume derivatives zero,
but a finite time step still leaves the small measured drift reported by the
page.
