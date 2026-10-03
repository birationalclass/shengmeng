module

public import Negativity.External.Laurent.ProjectiveLaurentCechCategoricalTotalFiniteness

@[expose] public section

/-!
This module reuses the completed Laurent Cech calculation in
Vilin97/Autoformalization at commit 09497ebf6ee48ef49c4f3d24501954bc3a2855d6.
The original proof and its license are in Negativity/External/Laurent.
The conclusion concerns the explicit projective Laurent complex. No
comparison with the structure sheaf of an actual projective scheme,
proper cohomology theorem or formal-functions bound is asserted here.
-/

namespace Negativity
open LeanEval.AlgebraicGeometry.ProjectiveLaurentCech

/-- Final theorem, reused from the pinned external proof over arbitrary
commutative coefficient rings; no characteristic-zero hypothesis. -/
theorem imported_projective_laurent_cech_cohomology_finite {ι R : Type*} [Fintype ι] [LinearOrder ι]
    [CommRing R] [IsNoetherianRing R] (d : ℤ) (n : ℕ) :
    Module.Finite R ((laurentCechComplex (ι := ι) (R := R) d).homology n) :=
  laurentCechCategoricalHomologyFinite (ι := ι) (R := R) d n

end Negativity
