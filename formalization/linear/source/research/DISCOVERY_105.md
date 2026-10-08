# Actual coordinate fibers and projective linear sections

Library first: official mathlib TensorProduct.Basic, Nullstellensatz,
and LinearAlgebra.Projectivization.Basic documentation, then the pinned
sources at 2a885768dae569d938bb9ff3474da6a8753bb90a.

Reused AlgHom.liftEquiv, the audited polynomialZeroLocusPointEquiv,
Projectivization.mk_eq_mk_iff and mk_rep. Compatible source evaluations
are proved equivalent to maps from the actual tensor fiber, then to
actual cone solutions of Li(v)=wi. Homogeneity and the already derived
no-basepoint property normalize each actual projective section point
uniquely; this proves a bijection with the coordinate fiber.

The original V entry constructs the actual projection and a nonempty
good target open; projective section cardinality equals its generic
module rank. This is not an assumed fiber set or cardinality.

Remaining: generic rank equals the Hilbert leading-coefficient degree V,
simultaneous good selection/transversality required by the manuscript
Setup, global scheme comparisons, Section 4 uniform lifting and actual
intersection. The full theorem remains UNPROVED.
