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
local instance originalDegreeVeroneseProductValueLeftGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

/-- Restricting a regraded fraction and then comparing it with the
original chart gives the displayed fraction in the original localization. -/
theorem originalDegreeVeroneseProductValueLeft_mk
    {d e : ℕ} {f g : V} (hf : f ∈ P d) (hg : g ∈ P e)
    (n : ℕ) (a : V) (ha : a ∈ P (n • d)) :
    (originalDegreeVeroneseChartRingEquiv B q (SetLike.mul_mem_graded hf hg)
      (originalDegreeVeroneseChartRestrict B q f g hg (Away.mk P hf n a ha))).val =
    Localization.mk ((a * g ^ n : V) : S)
      (⟨((f * g : V) : S) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers ((f * g : V) : S)) := by
  let hfg : f * g ∈ P (d + e) := SetLike.mul_mem_graded hf hg
  have hfgS : ((f * g : V) : S) ∈ B (q * (d + e)) := hfg
  have hb : a * g ^ n ∈ P (n • (d + e)) := by
    rw [smul_add]
    exact SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n hg)
  have hbS' : ((a * g ^ n : V) : S) ∈ B (q * (n • (d + e))) := hb
  have hdeg : q * (n • (d + e)) = n • (q * (d + e)) := by
    simpa only [nsmul_eq_mul, Nat.cast_id] using Nat.mul_left_comm q n (d + e)
  have hbS : ((a * g ^ n : V) : S) ∈ B (n • (q * (d + e))) := hdeg ▸ hbS'
  calc
    _ = (originalDegreeVeroneseChartRingEquiv B q hfg
          (Away.mk P hfg n (a * g ^ n) hb)).val :=
      congrArg (fun y => (originalDegreeVeroneseChartRingEquiv B q hfg y).val)
        (originalDegreeVeroneseChartRestrict_mk B q hf hg n a ha)
    _ = (Away.mk B hfgS n ((a * g ^ n : V) : S) hbS).val :=
      congrArg (fun y => y.val) (originalDegreeVeroneseChartRingEquiv_mk B q hfg n hb hfgS hbS)
    _ = _ := Away.val_mk B n hfgS _ hbS

end LinearStudy
#check LinearStudy.originalDegreeVeroneseProductValueLeft_mk
#print axioms LinearStudy.originalDegreeVeroneseProductValueLeft_mk

