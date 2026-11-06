module
public import Linear.OriginalDegreeVeroneseCoefficientLocalizationAction
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



theorem localizedFractionMap_add
    {R T X Y : Type*} [CommSemiring R] [CommSemiring T]
    [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [Module T Y]
    {U : Submonoid R} {U' : Submonoid T}
    (φ : LocalizedModule U X → LocalizedModule U' Y)
    (i : X →+ Y) (δ : U → U')
    (hδ : ∀ s t, δ (s * t) = δ s * δ t)
    (hsmul : ∀ (s : U) (a : X), i (s • a) = δ s • i a)
    (hmk : ∀ a s, φ (LocalizedModule.mk a s) = LocalizedModule.mk (i a) (δ s))
    (x y : LocalizedModule U X) : φ (x + y) = φ x + φ y := by
  induction x, y using LocalizedModule.induction_on₂
  simp only [LocalizedModule.mk_add_mk, hmk, map_add, hsmul, hδ]

/-- The original inclusion is additive before localizing. -/
def originalDegreeVeroneseCoefficientInclAdd : W →+ M where
  toFun := fun x => x.val
  map_zero' := rfl
  map_add' := fun _ _ => rfl

theorem originalDegreeVeroneseCoefficientInclAdd_denominator_smul (f : V)
    (s : Submonoid.powers f) (a : W) :
    originalDegreeVeroneseCoefficientInclAdd B D hD q (s • a) =
      originalDegreeVeroneseCoefficientDenominator B q f s •
        originalDegreeVeroneseCoefficientInclAdd B D hD q a := rfl

/-- The specialized fraction-additivity proof. -/
def originalDegreeVeroneseCoefficientLocalization_add (f : V) :=
  @localizedFractionMap_add V S W M
    (inferInstanceAs (CommSemiring V)) (inferInstanceAs (CommSemiring S))
    (inferInstanceAs (AddCommMonoid W)) (inferInstanceAs (AddCommMonoid M))
    (Submodule.module W) (inferInstanceAs (Module S M))
    (Submonoid.powers f) (Submonoid.powers (f : S))
    (originalDegreeVeroneseCoefficientLocalization B D hD q f)
    (originalDegreeVeroneseCoefficientInclAdd B D hD q)
    (originalDegreeVeroneseCoefficientDenominator B q f)
    (originalDegreeVeroneseCoefficientDenominator_mul B q f)
    (originalDegreeVeroneseCoefficientInclAdd_denominator_smul B D hD q f)
    (originalDegreeVeroneseCoefficientLocalization_mk B D hD q f)

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientLocalization_add
#print axioms LinearStudy.originalDegreeVeroneseCoefficientLocalization_add

