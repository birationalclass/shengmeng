module
public import Linear.OriginalDegreeVeroneseChartRingEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open HomogeneousLocalization
universe u v
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (q : ℕ) [hq : Fact (0 < q)]
local instance originalDegreeVeroneseChartRingEquivMkGraded :
    GradedAlgebra (originalDegreeVeronesePiece B q) :=
  originalDegreeVeroneseGrading B q hq.out

/-- The degree-zero chart equivalence sends the actual original
numerator and denominator to their identical values. -/
theorem originalDegreeVeroneseChartRingEquiv_mk
    {d : ℕ} {f : originalDegreeVeroneseAlgebra B q}
    (hf : f ∈ originalDegreeVeronesePiece B q d)
    (n : ℕ) {a : originalDegreeVeroneseAlgebra B q}
    (ha : a ∈ originalDegreeVeronesePiece B q (n • d))
    (hfS : (f : S) ∈ B (q * d)) (haS : (a : S) ∈ B (n • (q * d))) :
    originalDegreeVeroneseChartRingEquiv B q hf
      (Away.mk (originalDegreeVeronesePiece B q) hf n a ha) =
      Away.mk B hfS n (a : S) haS := by
  apply val_injective _
  rw [originalDegreeVeroneseChartRingEquiv_val]
  exact originalDegreeVeroneseChartValue_mk B q hf n ha hfS haS

end LinearStudy
#check LinearStudy.originalDegreeVeroneseChartRingEquiv_mk
#print axioms LinearStudy.originalDegreeVeroneseChartRingEquiv_mk
