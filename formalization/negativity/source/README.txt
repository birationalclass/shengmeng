Negativity: coefficient core and conditional interfaces

This snapshot is NOT a complete geometric proof of the negativity lemma.
New algebraic norm/valuation and actual Cartier restriction/order proofs
are included. Hartshorne I.6 actual curve-point/valuation bijection and local-order
transport, exhaustive disjoint finite/infinity place classification, actual
curve principal degree zero, and Cartier principal-move degree independence
are proved; the compatible finite separable parameter is now constructed
from actual finite-type one-dimensional Scheme geometry. Actual complete
normal curves have principal degree zero and Cartier principal-move invariance
without a parameter input, in arbitrary characteristic. Actual global Cartier pullback degree for proper dominant complete normal
curves, including inseparable maps, is proved with actual fibers and
local equations. Actual Cartier curve intersection is now constructed; its
rational-move independence, contracted-curve zero, effective-divisor signs
and proper dominant curve degree formula are proved. Actual ambient principal
moving, zero-Weil intersection, integer additivity, arbitrary real-presentation
independence (including different generators and covers), effective real-divisor
intersection signs, and actual ambient Cartier/R-Cartier pullback composition
are now proved. Ambient curve normalization, geometric ample positivity,
full Chow construction and connected-fiber curve existence remain open.
Amber nodes on the website are explicit mathematical hypotheses or missing
geometric bridges, NOT new Lean axioms. Read the full theorem parameters.

Reproduce (Lean's elan and Git are required):
  lake update
  lake exe cache get
  lake build
  lake env lean CheckAxioms.lean

lean-toolchain pins Lean; lakefile.toml pins mathlib; lake-manifest.json pins
transitive dependencies. .lake is deliberately excluded from this archive.
Proof sources: see Negativity.lean for the complete module import list, and
CheckAxioms.lean / snapshot.json for the audited declarations and exact source locations.
