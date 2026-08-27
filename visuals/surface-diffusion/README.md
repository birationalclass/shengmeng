# BGN surface diffusion visualizer

The page reproduces the embedded mesh animation on slide 8/38 of
`sp电子科大.pdf` as an interactive WebGL experiment.  The browser trajectory is
not a cube-to-sphere morph: `tools/generate_bgn_trajectory.py` assembles and
solves the linear BGN parametric finite-element system at every time step.

## Numerical model

On the old triangulated surface `S^m`, the generator solves for the new nodal
map `X^(m+1)` and scalar mean curvature `H^(m+1)`:

```text
< ((X^(m+1)-X^m)/tau) . n^m, phi >_h
    - < grad_S H^(m+1), grad_S phi > = 0,

< H^(m+1) n^m, eta >_h
    + < grad_S X^(m+1), grad_S eta > = 0.
```

The implementation uses continuous piecewise-linear surface elements, the
cotangent stiffness matrix, and the triangle-wise mass-lumped normal coupling.
The implicit tangential velocity is part of the saddle-point solve; no
remeshing is performed.

The checked-in trajectory uses 602 vertices, 1,200 triangles, 320 time steps,
and `tau = 5e-5`.  The binary file contains every nodal state plus the measured
surface area, enclosed volume, triangle quality, and discrete energy defect.

## Regeneration

With NumPy and SciPy installed:

```bash
python3 tools/generate_bgn_trajectory.py
```

The command rewrites `trajectory.bin` and `trajectory-diagnostics.json` and
fails if surface area increases, the discrete energy inequality is violated,
or any triangle reverses orientation.

## Scope

This is the original linear BGN scheme displayed in the slide.  It is
unconditionally area stable and has implicit tangential mesh motion, but its
fully discrete form does not preserve volume exactly.  The page reports the
measured volume drift instead of hiding it.  Exact fully discrete volume
conservation belongs to the later semi-implicit-normal SP-PFEM of Bao and Zhao
(2021), which is cited on the page but is not substituted for the slide's
animation.
