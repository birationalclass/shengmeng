module
public import Linear.OriginalDegreeVeroneseChartValues
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
local instance originalDegreeVeroneseChartInjectivityGraded : GradedAlgebra (originalDegreeVeronesePiece B q) :=
  originalDegreeVeroneseGrading B q hq.out

omit hq in
theorem originalDegreeVeroneseAwayMap_injective
    (f : originalDegreeVeroneseAlgebra B q) :
    Function.Injective (Localization.awayMap (originalDegreeVeroneseAlgebra B q).val.toRingHom f) := by
  apply Localization.awayMap_injective_iff.mpr
  intro x hx
  have hx0 : x = 0 := Subtype.ext hx
  exact ⟨0, by rw [hx0, mul_zero]⟩

theorem originalDegreeVeroneseChartValue_injective
    (f : originalDegreeVeroneseAlgebra B q) :
    Function.Injective (originalDegreeVeroneseChartValue B q f) :=
  (originalDegreeVeroneseAwayMap_injective B q f).comp (val_injective _)

end LinearStudy
#check LinearStudy.originalDegreeVeroneseAwayMap_injective
#print axioms LinearStudy.originalDegreeVeroneseAwayMap_injective
#check LinearStudy.originalDegreeVeroneseChartValue_injective
#print axioms LinearStudy.originalDegreeVeroneseChartValue_injective
