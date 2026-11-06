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
local instance originalDegreeVeroneseChartRangeGraded : GradedAlgebra (originalDegreeVeronesePiece B q) :=
  originalDegreeVeroneseGrading B q hq.out

/-- The original and regraded degree-zero chart rings have the same
fractions in the same ordinary localization. -/
theorem originalDegreeVeroneseChartValue_range
    {d : ℕ} {f : originalDegreeVeroneseAlgebra B q}
    (hf : f ∈ originalDegreeVeronesePiece B q d) :
    Set.range (originalDegreeVeroneseChartValue B q f) =
      Set.range (algebraMap (Away B (f : S)) (Localization.Away (f : S))) := by
  have hfS : (f : S) ∈ B (q * d) := hf
  have degree (n : ℕ) : q * (n • d) = n • (q * d) := by
    simp only [nsmul_eq_mul, Nat.cast_id]
    exact Nat.mul_left_comm q n d
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (originalDegreeVeronesePiece B q) hf z
    have ha' : (a : S) ∈ B (q * (n • d)) := ha
    have haS : (a : S) ∈ B (n • (q * d)) := degree n ▸ ha'
    refine ⟨Away.mk B hfS n (a : S) haS, ?_⟩
    exact (originalDegreeVeroneseChartValue_mk B q hf n ha hfS haS).symm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective B hfS z
    have ha' : a ∈ B (q * (n • d)) := (degree n).symm ▸ ha
    let aV : originalDegreeVeroneseAlgebra B q :=
      ⟨a, originalDegreeVeroneseAlgebra_mem_of_mem B q (n • d) ha'⟩
    have haV : aV ∈ originalDegreeVeronesePiece B q (n • d) := ha'
    refine ⟨Away.mk (originalDegreeVeronesePiece B q) hf n aV haV, ?_⟩
    exact originalDegreeVeroneseChartValue_mk B q hf n haV hfS ha

end LinearStudy
#check LinearStudy.originalDegreeVeroneseChartValue_range
#print axioms LinearStudy.originalDegreeVeroneseChartValue_range
