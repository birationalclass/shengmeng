# Library discovery: finite linear projection good opens

Target: the actual linear normalization from checkpoints 101–102 must have
a nonempty target open whose whole source preimage is smooth/unramified
and avoids a chosen proper source closed set. This supports simultaneous
good target selection in the original Setup; it is not the completed Setup.

Online official mathlib documentation inspected:
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Unramified/Field.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Integral.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/IsAlgClosed/Basic.html

Pinned local sources checked at mathlib commit 2a885768dae569d938bb9ff3474da6a8753bb90a:
IsFractionRing.liftAlgHom/lift_algebraMap; isAlgebraic_iff'; comap_isAlgebraic_iff;
Algebra.FormallyUnramified.of_isSeparable; RingHom.FormallyUnramified.comp;
Module.isTorsionFree_iff_algebraMap_injective. Reused the already audited
project GenericSmoothUnramifiedOpen, TargetGoodLoci and source-closed avoidance.

These library results cover separability and localization. The uncovered bridge
constructs the actual fraction map of the finite injective linear projection,
proves its algebraicity and characteristic-zero separability, then applies the
same generic-open and target-avoidance mechanisms to the original V.
No finite fraction extension, good fiber, smooth V, basepoint-free tuple or
generic unramification is assumed as a new input.

Exact remaining obligations: reduced generic linear-section point count and
its degree V identification; projective section/coordinate comparison and
simultaneous avoidance; Section 4 canonical-sheaf lifting and actual intersection.
The full Linearity Theorem remains UNPROVED.
