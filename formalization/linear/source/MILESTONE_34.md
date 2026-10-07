# Milestone 34: actual formal-to-polynomial fiber comparison

For any field, finite variable set, Artinian polynomial equation quotient and a rational residue algebra map, the point coordinates are derived from the images of the polynomial variables. Its actual ambient prime ideal is proved to be the coordinate evaluation kernel.

The actual translated formal polynomial ideal is defined using the reused translation homomorphism. Its power-series quotient is proved isomorphic to the original equation quotient localized at the residue kernel. This constructs the comparison rather than assuming a ring equivalence. The map on every original polynomial class is proved explicitly.

`polynomial_formal_socle_generator_descends` transports a specified formal nilradical-annihilator generator to the same original polynomial class in the original local fiber. It still assumes the precise formal-generator property; deriving it for Theta from the manuscript's finite-flat thickened geometric setup is unfinished.

Reused the audited ambient-completion quotient and actual quotient/localization comparison. No new foundational implementation was required beyond composition and the canonical-class verification. The full Linearity Theorem is still unproved.
