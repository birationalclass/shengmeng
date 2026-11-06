module
public import Linear.OriginalDegreeVeroneseChartRange
public import Linear.OriginalDegreeVeroneseChartInjectivity
public import Linear.OriginalRingEquivOfEqualImages
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
local instance originalDegreeVeroneseChartRingEquivGraded : GradedAlgebra (originalDegreeVeronesePiece B q) :=
  originalDegreeVeroneseGrading B q hq.out

/-- A homogeneous chart and its Veronese chart have the same
degree-zero ring through their common fractions. -/
def originalDegreeVeroneseChartRingEquiv
    {d : ℕ} {f : originalDegreeVeroneseAlgebra B q}
    (hf : f ∈ originalDegreeVeronesePiece B q d) :
    Away (originalDegreeVeronesePiece B q) f ≃+* Away B (f : S) :=
  originalRingEquivOfEqualImages
    (originalDegreeVeroneseChartValue B q f)
    (algebraMap (Away B (f : S)) (Localization.Away (f : S)))
    (originalDegreeVeroneseChartValue_injective B q f)
    (val_injective _)
    (SetLike.coe_injective (originalDegreeVeroneseChartValue_range B q hf))

theorem originalDegreeVeroneseChartRingEquiv_val
    {d : ℕ} {f : originalDegreeVeroneseAlgebra B q}
    (hf : f ∈ originalDegreeVeronesePiece B q d)
    (z : Away (originalDegreeVeronesePiece B q) f) :
    (originalDegreeVeroneseChartRingEquiv B q hf z).val =
      originalDegreeVeroneseChartValue B q f z :=
  originalRingEquivOfEqualImages_apply
    (originalDegreeVeroneseChartValue B q f)
    (algebraMap (Away B (f : S)) (Localization.Away (f : S)))
    (originalDegreeVeroneseChartValue_injective B q f)
    (val_injective _)
    (SetLike.coe_injective (originalDegreeVeroneseChartValue_range B q hf)) z

end LinearStudy
#check LinearStudy.originalDegreeVeroneseChartRingEquiv
#print axioms LinearStudy.originalDegreeVeroneseChartRingEquiv
#check LinearStudy.originalDegreeVeroneseChartRingEquiv_val
#print axioms LinearStudy.originalDegreeVeroneseChartRingEquiv_val
