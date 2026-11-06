module
public import Linear.OriginalDegreeVeroneseProductValueLeft
public import Linear.OriginalDegreeVeroneseProductValueRight
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
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeroneseChartRefinementGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

/-- The Veronese chart comparison commutes with both original
product-chart fraction maps. -/
theorem originalDegreeVeroneseChartRingEquiv_awayMap
    {d e : ℕ} {f g : V} (hf : f ∈ P d) (hg : g ∈ P e)
    (z : Away P f) :
    originalDegreeVeroneseChartRingEquiv B q (SetLike.mul_mem_graded hf hg)
      (originalDegreeVeroneseChartRestrict B q f g hg z) =
    originalDegreeVeroneseAmbientChartRestrict B q f g hg
      (originalDegreeVeroneseChartRingEquiv B q hf z) := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective P hf z
  apply val_injective _
  exact (originalDegreeVeroneseProductValueLeft_mk B q hf hg n a ha).trans
    (originalDegreeVeroneseProductValueRight_mk B q hf hg n a ha).symm

end LinearStudy
#check LinearStudy.originalDegreeVeroneseChartRingEquiv_awayMap
#print axioms LinearStudy.originalDegreeVeroneseChartRingEquiv_awayMap

