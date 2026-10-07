# Local milestone 48: polynomial fiber socle and the actual local pullback

The exact global LinearityTheoremGoal remains UNPROVED.

Constructed an actual ring equivalence from the smooth-coordinate formal
fiber quotient to the localization of the original Artinian polynomial fiber.
The image of every polynomial class is proved to be its actual localized
class. No comparison equivalence is an input.

Combined equation and arbitrary parameter quotients using mathlib's actual
double-quotient equivalence, including its action on the Jacobian. The
relative socle theorem transfers to this single ambient fiber quotient.

Constructed the point-local quotient pullback induced by the actual polynomial
substitution map. Preservation of the extended equation ideal and the local
ring homomorphism property are proved, as is the reduction formula for every
polynomial. Under essential finite type and formal unramifiedness of this
specific constructed map, target local parameters pull back to generators
of the actual smooth reduced source maximal ideal. The algebra structure is
the constructed map's toAlgebra, not an arbitrary algebra input.

Finally smooth_polynomial_local_fiber_socle derives a nonzero generator of
Ann(nilradical) in the original polynomial fiber localization from actual
point-local source/target equation generators, a source Jacobian unit minor,
the radical pullback equality, the actual fiber ideal, and parameter generation.
The formal normal derivative determinant differs from the normal polynomial
Jacobian determinant by a proved unit factor. No socle-generation conclusion
or opaque formal-coordinate map is assumed in this theorem.

Remaining: derive the smooth presentations, minor, target parameters and
unramifiedness from the manuscript geometric setup; compare the locally
generated Jacobian with the single common Theta in projective charts; prove
generic fiber/cardinality, uniform global duality/Serre lifting and actual
geometric Bezout. The local polynomial Jacobian may still depend on the chosen
target local generators. This milestone does not silently identify it with
the globally chosen Theta.

Library discovery: official mathlib AtPrime documentation (online) and exact
pinned local AtPrime/Quotient signatures; official pinned GitHub quotient
source record in research/double-quotient-discovery.json. The compiler now uses
the standard --stdin and --setup APIs with exact source bytes, original module
names and file names, avoiding the Windows sandbox path-canonicalization
failure without changing compiler trust or dependencies. Builds, declaration
range extraction and full axiom auditing use this same pinned compiler.

Live release remains 18; pending release 19 has not been pushed. The user's
new retry authorization concerns local compilation, not GitHub publication.
