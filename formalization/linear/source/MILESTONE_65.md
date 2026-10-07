# Milestone 65: nonempty unramified open on the actual cone

The Linearity Theorem remains unproved. Starting with the original positive-
degree surjective projective map and the totally invariant integral homogeneous
equations, this checkpoint gives a nonzero element of the actual homogeneous
coordinate domain whose principal open is formally unramified over the source
coordinate ring through the actual induced map.

The coordinate map is of finite type because its target is finite type over
the complex field and the map preserves that field. Its actual fraction-field
map from milestone 64 gives nonramification after passing to the generic point.
The canonical fraction-ring/localization-at-zero isomorphism transports this
property to the genuine generic local ring. The mathlib unramified-locus
theorem then spreads it to a nonempty principal open.

The open is in the affine cone. Its defining element is not asserted to be
homogeneous. Descent to projective affine charts and construction of entire
general unramified fibers, including cardinalities, remain unfinished.
No independent generic nonramification or finite-type assumption is introduced
in the concrete projective-coordinate result.
