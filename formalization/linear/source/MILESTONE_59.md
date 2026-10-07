# Milestone 59: actual rational projective chart and formal ideal comparison

The full Linearity Theorem remains unproved.

Construct the actual polynomial coordinate-ratio map into the localization at
its denominator, its point evaluation, and its translation into the actual
formal power-series ring. Prove the point-prime correspondence, invertibility
criterion, and equality with the existing formal coordinate ratios.

Construct point-local quotient pullbacks for distinct actual source and target
rings and ideals. Reuse mathlib's iterated-localization equivalence to identify
the actual localized point quotient with the original point quotient, including
the polynomial evaluation formula.

Prove homogeneous polynomial scaling in an arbitrary coefficient algebra.
Homogeneous ideal generators acquire invertible factors depending on their
degrees, so the ideal pulled back via coordinate ratios is exactly the
homogeneous pullback ideal mapped into the denominator chart. The original
projective total invariance therefore gives the power sandwich and the radical
comparison after every actual ring map. Ideal preservation is derived here.

In particular, construct the actual map into the source formal ring and prove
the formal radical comparison. Target point-local generators transfer to this
formal rational pullback, so the mapped-ideal/equation comparison is proved,
rather than supplied as an opaque input. The algebraic chart map agrees with
the existing dehomogenization used for degree and homogeneous relations.

Still open: combine these actual maps with source and target smooth coordinate
changes and actual unramified projective fibers; relate differential rank to
geometric dimension; construct general smooth/etale fibers and their q^r point
counts; establish uniform global Serre/duality lifting, Cartier/Bezout estimates
and scheme/coordinate theorem comparison. The manuscript is unchanged.
