# Checkpoint 106: the same linear projection controls sections and growth

The pinned mathlib commit is `2a885768dae569d938bb9ff3474da6a8753bb90a`.
Existing homogeneous-component, finite-module, finite-dimensional and filtered-quotient APIs were searched and reused. No project axiom or theorem-specific assumption was added.

The private compiler logs bind their exact source hashes to exit code 0:

- `log-linear-projection-graded-control2.log`: a homogeneous generic basis, a common denominator and coefficient degree bounds for the actual finite degree-one projection.
- `log-linear-projection-filtered-growth3.log`: injective bounded combinations and two-sided filtered dimension estimates retaining the actual generic module rank.

The combined entry `projective_exists_same_linear_section_generic_growth` constructs everything from the original integral projective `V`. Its actual projective section cardinality and growth inequalities belong to the same projection; they are not independently chosen models.

This does not yet identify the generic rank with `degree V` defined by the Hilbert leading coefficient. Simultaneous good target selection/transversality, global Scheme comparisons, the actual Section 4 fixed-degree lifting and the actual geometric intersection bound remain open. The full manuscript theorem is not proved.
