# Local checkpoint 52: derived formal normal coordinates

The global LinearityTheoremGoal remains UNPROVED. This is a local-only checkpoint.

An injective selection of normal coordinates is extended to an actual
permutation of ALL ambient coordinates, preserving their selected order.
Polynomial evaluation and derivative evaluation under this permutation are
proved equal to their original-coordinate values. This connects the
nonzero minor constructed in checkpoint 51 to the normal-coordinate minor
needed by the existing formal inverse theorem.

Point translation commutes with coordinate renaming. Applying this proved
identity to the actual extended local ideal proves its generated formal
ideal in the new coordinates. The constructed inverse formal coordinate
map sends that original ideal precisely to the normal-variable ideal.

The existence theorem smooth_point_has_formal_normal_coordinates assumes
only the actual rational point prime, containment of the polynomial ideal,
formal smoothness of its actual localized quotient and nonzero localized
ideal. It CONSTRUCTS the numbers of coordinates, their permutation, actual
polynomial equations, point vanishing, a unit normal minor and the formal
normal-ideal equality. No equations, minor, coordinate map or ideal equality
is supplied as an opaque input. Codimension zero is explicitly excluded by
the nonzero localized ideal assumption, and a zero-size generator family
is proved impossible from that assumption.

Still open: the constructed tangent/normal counts must be connected to
the manuscript's geometric dimension, and common coordinates over all
chosen points must be justified. The geometric smooth locus, radical and
unramified parameter conditions, generic fibers/cardinality, uniform
proper-duality/Serre polynomial lifting and geometric Bezout remain
unfinished. A constructed formal ambient ideal presentation does not
alone prove all those geometric inputs or the global theorem.
