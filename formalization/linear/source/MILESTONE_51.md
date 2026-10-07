# Local checkpoint 51: a polynomial Jacobian minor from smoothness

The global LinearityTheoremGoal is UNPROVED. This checkpoint is local only.

For an actual polynomial ideal I contained in the rational point prime P,
assume the actual localized quotient is formally smooth over the base field.
The new theorem `exists_smooth_polynomial_jacobian_generators_at_point`
CONSTRUCTS a finite family G of actual polynomials generating I locally,
vanishing at that point, and a choice of distinct original coordinates with
nonzero evaluated Jacobian determinant. Neither an ideal presentation,
conormal basis, residue map, full-rank Jacobian nor a nonzero minor is assumed.

The proof uses the previous constructed conormal basis, the actual
cotangent-complex splitting supplied by smoothness, and its base change to
the residue field. The split map is proved injective after base change. Its
coordinate entries are identified with the actual polynomial derivatives,
using the localized ambient differential basis. Basis selection supplies
original coordinate columns for the nonzero minor. The point evaluation map
on the localization and quotient is explicitly constructed from the
localization universal property; compatibility with polynomial evaluation
and vanishing of the original ideal are proved.

The number of generators is not yet identified with the manuscript's
geometric codimension. A coordinate permutation, common chart choices,
the original geometric smooth locus, radical and parameter conditions,
generic finite fibers/cardinalities, uniform global-duality/Serre lifting,
and geometric Bezout remain unfinished obligations. This result is a
genuine embedded local smooth presentation statement, not a proof of those
remaining geometric facts or of the global Linearity Theorem.
