module
public import Linear.OriginalDegreeVeroneseProductChartCompat
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
local instance originalDegreeVeroneseProductValueRightGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

/-- Comparing a regraded fraction and then restricting on the original
charts gives the displayed fraction in the original localization. -/
theorem originalDegreeVeroneseProductValueRight_mk
    {d e : ℕ} {f g : V} (hf : f ∈ P d) (hg : g ∈ P e)
    (n : ℕ) (a : V) (ha : a ∈ P (n • d)) :
    (originalDegreeVeroneseAmbientChartRestrict B q f g hg
      (originalDegreeVeroneseChartRingEquiv B q hf (Away.mk P hf n a ha))).val =
    Localization.mk ((a * g ^ n : V) : S)
      (⟨((f * g : V) : S) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers ((f * g : V) : S)) := by
  have hfS : (f : S) ∈ B (q * d) := hf
  have haS' : (a : S) ∈ B (q * (n • d)) := ha
  have hdeg : q * (n • d) = n • (q * d) := by
    simpa only [nsmul_eq_mul, Nat.cast_id] using Nat.mul_left_comm q n d
  have haS : (a : S) ∈ B (n • (q * d)) := hdeg ▸ haS'
  have hgS : (g : S) ∈ B (q * e) := hg
  have hfgS : ((f * g : V) : S) ∈ B (q * d + q * e) := SetLike.mul_mem_graded hfS hgS
  have hbS : (a : S) * (g : S) ^ n ∈ B (n • (q * d + q * e)) := by
    rw [smul_add]
    exact SetLike.mul_mem_graded haS (SetLike.pow_mem_graded n hgS)
  calc
    _ = (originalDegreeVeroneseAmbientChartRestrict B q f g hg
        (Away.mk B hfS n (a : S) haS)).val :=
      congrArg (fun y => (originalDegreeVeroneseAmbientChartRestrict B q f g hg y).val)
        (originalDegreeVeroneseChartRingEquiv_mk B q hf n ha hfS haS)
    _ = (Away.mk B hfgS n ((a : S) * (g : S) ^ n) hbS).val :=
      congrArg (fun y => y.val) (originalDegreeVeroneseAmbientChartRestrict_mk B q hg hfS n (a : S) haS)
    _ = _ := Away.val_mk B n hfgS _ hbS

end LinearStudy
#check LinearStudy.originalDegreeVeroneseProductValueRight_mk
#print axioms LinearStudy.originalDegreeVeroneseProductValueRight_mk

