# Milestone 67: actual rational chart pullback and a nonempty unramified open

The final Linearity Theorem remains unproved.

On an explicitly inhabited standard chart, the original homogeneous projective map now induces an actual endomorphism of the chart fraction field. The actual field map agrees with the dehomogenized coordinate ratios f_i/f_0. Projective surjectivity implies that its denominator is nonzero in the chart coordinate domain.

The rational polynomial map descends to that coordinate domain with values in its denominator localization. Its comparison with the actual fraction-field map is proved, rather than assumed. Generic nonramification then supplies a nonzero principal open within this source chart on which this actual ring map is formally unramified.

This does not assert that a whole projective fiber lies in that open, that the map is finite etale there, or that a fiber has q^r points. Smooth source/target point-local comparisons, geometric degree, uniform global lifting and geometric Bezout remain unfinished.

The source uses actual mathlib quotient rings, localizations, fraction fields and induced maps. Private compilation checked exact types and found only propext, Classical.choice and Quot.sound. Full-project compilation and axiom auditing determine the recorded checkpoint status.
