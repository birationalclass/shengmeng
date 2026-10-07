# Local checkpoint 50: smooth embedded polynomial generators

The global LinearityTheoremGoal remains UNPROVED. This is a local checkpoint;
no GitHub push or deployment is claimed.

The new construction starts with an actual polynomial ideal localized at a
prime containing it, and formal smoothness of the actual localized quotient.
The ambient localization is formally smooth by the existing library instance.
The actual cotangent-complex splitting makes the conormal module projective;
finite generation and locality make it free. A basis is constructed, lifted
to ideal elements, and Nakayama proves that these generate the original local
ideal. Localization denominators are cleared to produce actual POLYNOMIAL
generators. Multiplying basis vectors by the corresponding quotient units
retains the basis property. Neither local generators nor conormal freeness
are input assumptions in the final existence theorem.

The actual localized ambient differential basis is also constructed from
mathlib's polynomial basis and the formally-etale localization equivalence.
Its coefficients on a localized polynomial differential are proved to equal
the localized partial derivatives. This equality survives quotient base
change. Separately, original-coordinate nonzero maximal minors are selected
from any row-independent rectangular matrix using the existing spanning and
basis-selection results, without a supplied inverse or a minor hypothesis.

Still to connect: cotangent splitting and residue base change to the actual
Jacobian matrix of these generators, the number of equations to geometric
codimension, and these local smooth presentations to the manuscript's common
coordinate choices. Radical/parameter conditions, generic fiber geometry,
uniform global duality/Serre lifting and geometric Bezout inputs remain open.

The complete project build and declaration/type/axiom/source-range audit must
pass before the checkpoint is recorded. No sorry or new axioms are used.
