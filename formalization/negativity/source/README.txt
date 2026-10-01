Negativity: coefficient core and conditional interfaces

This snapshot is NOT a complete geometric proof of the negativity lemma.
Amber nodes on the website are explicit mathematical hypotheses or missing
geometric bridges, NOT new Lean axioms. Read the full theorem parameters.

Reproduce (Lean's elan and Git are required):
  lake update
  lake exe cache get
  lake build
  lake env lean CheckAxioms.lean

lean-toolchain pins Lean; lakefile.toml pins mathlib; lake-manifest.json pins
transitive dependencies. .lake is deliberately excluded from this archive.
Proof source: Negativity/Numerical.lean, Coefficients.lean, Interfaces.lean, Descent.lean, GeometricCycles.lean, Projection.lean, LocalPushPull.lean, LocalGeometry.lean, NormalBirational.lean, AffineSections.lean, CurveDegree.lean, PrincipalDivisors.lean, PullbackDiagram.lean, PointPullback.lean, CurveSelection.lean, LocalConnectedness.lean.
