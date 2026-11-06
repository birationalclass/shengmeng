module
public import Linear.OriginalDegreeVeroneseChartRingEquivMk
public import Linear.OriginalDegreeVeroneseCoefficientLocalization
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
local instance originalDegreeVeroneseCoefficientScalarValueGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out

/-- The chart-ring scalar has the identical ordinary localization value. -/
theorem originalDegreeVeroneseCoefficientScalarValue_mk
    {d : ℕ} {f : V} (hf : f ∈ P d) (n : ℕ) (a : V) (ha : a ∈ P (n • d)) :
    (originalDegreeVeroneseChartRingEquiv B q hf (Away.mk P hf n a ha)).val =
      Localization.mk (a : S) (originalDegreeVeroneseCoefficientDenominator B q f
        (⟨f^n, ⟨n, rfl⟩⟩ : Submonoid.powers f)) := by
  have hfS : (f : S) ∈ B (q*d) := hf
  have haS : (a : S) ∈ B (n • (q*d)) := by
    change (a : S) ∈ B (q * (n • d)) at ha
    have he : q * (n • d) = n • (q*d) := Nat.mul_left_comm q n d
    exact he ▸ ha
  exact congrArg (fun c : Away B (f : S) => c.val)
    (originalDegreeVeroneseChartRingEquiv_mk B q hf n ha hfS haS)

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientScalarValue_mk
#print axioms LinearStudy.originalDegreeVeroneseCoefficientScalarValue_mk

