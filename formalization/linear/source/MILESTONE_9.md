# Milestone 9: actual diagonal Jacobian construction

The full Linearity Theorem remains unproved. This milestone constructs
a diagonal difference determinant mapping to the actual derivative
Jacobian, without assuming a Jacobian identity or nonvanishing.

NilpotentEvaluation.lean constructs actual power-series evaluation into
commutative rings at finite nilpotent tuples. Its constant/variable
formulas and compatibility with arbitrary ring maps are proved using
mathlib evaluation and internal discrete uniformities.

NilpotentEvaluationUnique.lean gives an algebraic finite-box truncation
proof: homomorphisms with nilpotent variable images are determined by
constants and variables, without continuity assumptions. Truncation can
preserve both a series value and the values of its actual derivatives.

PolynomialDiagonal.lean constructs difference coefficients inductively
and proves their diagonal images equal actual partial derivatives.
PowerSeriesDiagonal.lean extends this construction via finite-box
truncation and constructs a matrix whose determinant annihilates the
variable-difference ideal and maps to the derivative Jacobian.

ArtinianDiagonal.lean applies it to the actual quotient Q=K[[X]]/(H),
with zero-constant equations and Artinianity. Coordinate nilpotence is
derived. Coordinate differences generate the actual kernel of tensor
multiplication, using mathlib's KaehlerDifferential ideal theorem. Thus
the constructed determinant annihilates the true diagonal ideal and
its multiplication image is the actual derivative Jacobian.

These results hold over arbitrary fields as specified by their exact
types. The last construction does not require regularity, and DOES NOT
prove nonvanishing, a socle generator identity or the residue/trace
identity. Those remain the next mathematical obligations; no geometric
or relative-Jacobian target is labeled complete.

Library-first discovery: official MvPowerSeries Evaluation/Trunc/Derivative,
MvPolynomial PDeriv and Kaehler Basic documentation, plus the pinned
source types. Existing evaluation, truncation, derivative-coercion,
polynomial induction/extensionality and diagonal-ideal APIs are reused.
No compatible complete Jacobian/trace implementation was found in these
focused searches; this is not a universal nonexistence claim.

Later focused discovery located LinearMap.trace_eq_contract_apply and
dualTensorHom in official Trace/Contraction documentation; these APIs
are the next route to the diagonal-to-trace comparison.

Build, axiom and release counts are generated from snapshot.json and
validation.json. Research experiments are excluded from source counts
and the published archive. Deployment evidence is recorded separately.
