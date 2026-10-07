# Local milestone 47: actual reduced smooth coordinates and Jacobian comparison

The exact projective LinearityTheoremGoal remains unproved.

Actual point-local polynomial generators and an invertible polynomial Jacobian
minor now construct a map from the actual smooth local quotient to tangent
power series. Its maximal ideal maps to the actual power-series maximal ideal.
For an essentially finite type, formally unramified local algebra, parameter
generation follows from mathlib's unramified maximal-ideal theorem; it is not
assumed as a conclusion. Connecting this local algebra to the original map's
geometric étale locus remains an obligation.

The polynomial derivation chain rule is proved for actual polynomial inputs
and the constructed smooth formal map. Its normal coordinate Jacobian has
unit determinant. The actual normal polynomial Jacobian and the formal normal
Jacobian therefore differ by this unit, including after quotienting by any
actual ideal. Nonvanishing and the generated principal ideal transfer.

Reused primary pinned mathlib code: RingTheory/Unramified/LocalRing.lean,
RingTheory/AdicCompletion/LocalRing.lean, RingTheory/Ideal/Quotient/Operations.lean,
Algebra/MvPolynomial/PDeriv.lean, and the localization lift API. Online
discovery records remain in research/etale-parameter-discovery.json.

No project sorry, admit or custom axioms are introduced. Conditional input
scopes remain explicit. A full build and declaration/axiom audit are required
before counting this milestone as verified. Live release remains milestone 18;
release 19 remains unpushed after automatic-approval timeouts, with retry approval
pending. Local mathematical work continues independently.
