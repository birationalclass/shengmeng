module
public import Linear.OriginalDegreeVeroneseCoefficientLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
universe u v w
variable {K : Type u} {S : Type v} {M : Type w}
variable [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ (n : ℕ) (d : ℤ) (c : S), c ∈ B n →
  ∀ x : M, x ∈ D d → c • x ∈ D ((n : ℤ) + d))
variable (q : ℕ)
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "W" => originalDegreeVeroneseCoefficient B D hD q



attribute [local instance] LocalizedModule.moduleOfIsLocalization

theorem originalDegreeVeroneseCoefficientDenominator_mul (f : V)
    (s t : Submonoid.powers f) :
    originalDegreeVeroneseCoefficientDenominator B q f (s * t) =
      originalDegreeVeroneseCoefficientDenominator B q f s *
        originalDegreeVeroneseCoefficientDenominator B q f t :=
  Subtype.ext rfl

/-- Scalar fractions act on original and regraded coefficients through
their identical numerator and denominator values. -/
theorem originalDegreeVeroneseCoefficientLocalization_mk_smul (f : V)
    (c : V) (s : Submonoid.powers f) (x : LocalizedModule (Submonoid.powers f) W) :
    originalDegreeVeroneseCoefficientLocalization B D hD q f (Localization.mk c s • x) =
      Localization.mk (c : S) (originalDegreeVeroneseCoefficientDenominator B q f s) •
        originalDegreeVeroneseCoefficientLocalization B D hD q f x := by
  induction x using LocalizedModule.induction_on
  simp only [LocalizedModule.mk_smul_mk, originalDegreeVeroneseCoefficientLocalization_mk,
    originalDegreeVeroneseCoefficientDenominator_mul]
  rfl

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientDenominator_mul
#print axioms LinearStudy.originalDegreeVeroneseCoefficientDenominator_mul
#check LinearStudy.originalDegreeVeroneseCoefficientLocalization_mk_smul
#print axioms LinearStudy.originalDegreeVeroneseCoefficientLocalization_mk_smul

