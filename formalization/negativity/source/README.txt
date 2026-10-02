Negativity: coefficient core and conditional interfaces

This snapshot is NOT a complete geometric proof of the negativity lemma.
New algebraic norm/valuation and actual Cartier restriction/order proofs
are included. Hartshorne I.6 actual curve-point/valuation bijection and local-order
transport are proved. Finite/infinity place classification and principal-move
degree independence, geometric ample positivity, full Chow construction
and connected-fiber curve existence remain open.
Amber nodes on the website are explicit mathematical hypotheses or missing
geometric bridges, NOT new Lean axioms. Read the full theorem parameters.

Reproduce (Lean's elan and Git are required):
  lake update
  lake exe cache get
  lake build
  lake env lean CheckAxioms.lean

lean-toolchain pins Lean; lakefile.toml pins mathlib; lake-manifest.json pins
transitive dependencies. .lake is deliberately excluded from this archive.
Proof source: Negativity/Numerical.lean, Coefficients.lean, Interfaces.lean, Descent.lean, GeometricCycles.lean, Projection.lean, LocalPushPull.lean, LocalGeometry.lean, NormalBirational.lean, AffineSections.lean, CurveDegree.lean, PrincipalDivisors.lean, PullbackDiagram.lean, PointPullback.lean, CurveSelection.lean, LocalConnectedness.lean, CodimensionOne.lean, HartshorneGraph.lean, RelativeNumerics.lean, RationalProductFormula.lean, NormalSections.lean, FractionFieldOrders.lean, CodimensionSupport.lean, CartierAtlas.lean, CartierPullback.lean, CartierPushPull.lean, StrictTransform.lean, DivisorPullback.lean, SeparableNorm.lean, FiniteNormalGeometry.lean, CartierSupport.lean, RationalCone.lean, CartierCombinations.lean, RealCartierDecomposition.lean, NormalExtension.lean, CartierEffectivity.lean, CartierVanishing.lean, RealCartierPullback.lean, NormDivisor.lean, RationalDivisor.lean, InfinityNorm.lean, FunctionFieldProductFormula.lean, CartierDegree.lean, CartierCurveRestriction.lean, RealCartierCurveDegree.lean, CartierCurveMoving.lean, RationalInfinityResidue.lean, FunctionFieldDegree.lean, ValuationCenters.lean, NormalCurveValuations.lean, ValuationOrderTransport.lean.
