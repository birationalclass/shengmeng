# Milestone 27: actual projective chart comparison

The full Linearity Theorem remains **UNPROVED**. The manuscript is unchanged.

Dehomogenization is constructed using mathlib's actual `finSuccEquiv` and polynomial evaluation at 1. Its degree is bounded by the original total degree. For a degree-q homogeneous polynomial, its degree-q dehomogenized component is the zeroth coefficient in that equivalence, and its evaluation is the original polynomial's evaluation on the boundary hyperplane. Nonzero boundary coefficients give exact dehomogenized degree q.

Homogeneous evaluation is proved to equal the affine evaluation times the first coordinate to the homogeneous degree. Any affine bounded-degree weighted relation therefore yields a homogeneous relation, with weights divided by those nonzero coordinate powers and still nonzero.

For the actual `HomogeneousEndomorphism` and `Projectivization` objects, a coordinate hyperplane avoiding the fiber of the standard projective point gives the no-infinity condition. Together with nonzero individual boundary forms this implies the actual highest parts have origin-only common zero locus.

Hyperplane existence for the geometric fiber, highest-part regularity, completed smooth charts and geometric local socle compatibility remain unfinished. The no-infinity and coordinate conditions are explicit hypotheses rather than silently derived facts.

Primary reused APIs inspected online and in the pinned source: `MvPolynomial.eval_polynomial_eval_finSuccEquiv`, `totalDegree_coeff_finSuccEquiv_add_le`, `IsHomogeneous.finSuccEquiv_coeff_isHomogeneous`, and actual projectivization representative equality.
