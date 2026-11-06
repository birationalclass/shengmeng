module
public import Linear.OriginalDegreeVeroneseCoefficientLocalizationAction
public import Linear.OriginalDegreeVeroneseCoefficientScalarValue
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
variable (q : ℕ) [hq : Fact (0 < q)]
local notation "V" => originalDegreeVeroneseAlgebra B q
local notation "W" => originalDegreeVeroneseCoefficient B D hD q



open HomogeneousLocalization
local notation "P" => originalDegreeVeronesePiece B q
local instance originalDegreeVeroneseCoefficientChartScalarGraded : GradedAlgebra P :=
  originalDegreeVeroneseGrading B q hq.out
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- A homogeneous scalar in the chart is represented by one fraction, so
a compatible map of localized modules respects all of its scalar actions. -/
theorem localizedModule_chartScalar_compare
    {F R T X Y : Type*} [Field F] [CommRing R] [CommRing T] [Algebra F R]
    [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module T Y]
    (A : ℕ → Submodule F R) [GradedAlgebra A]
    {d : ℕ} {f : R} (hf : f ∈ A d) (g : T)
    (i : R → T) (δ : Submonoid.powers f → Submonoid.powers g)
    (χ : Away A f → Localization.Away g)
    (φ : LocalizedModule (Submonoid.powers f) X → LocalizedModule (Submonoid.powers g) Y)
    (hχ : ∀ n a ha, χ (Away.mk A hf n a ha) = Localization.mk (i a)
      (δ (⟨f^n, ⟨n,rfl⟩⟩ : Submonoid.powers f)))
    (hφ : ∀ (a : R) (s : Submonoid.powers f) (x : LocalizedModule (Submonoid.powers f) X),
      φ (Localization.mk a s • x) = Localization.mk (i a) (δ s) • φ x)
    (c : Away A f) (x : LocalizedModule (Submonoid.powers f) X) :
    φ (c.val • x) = χ c • φ x := by
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective A hf c
  rw [Away.val_mk, hχ]
  exact hφ a ⟨f^n,⟨n,rfl⟩⟩ x

/-- The localized coefficient inclusion is semilinear over the actual
Veronese chart ring equivalence. -/
def originalDegreeVeroneseCoefficientLocalization_chart_smul
    {d : ℕ} {f : V} (hf : f ∈ P d) :=
  @localizedModule_chartScalar_compare K V S W M
    (inferInstanceAs (Field K)) (inferInstanceAs (CommRing V)) (inferInstanceAs (CommRing S))
    (inferInstanceAs (Algebra K V))
    (inferInstanceAs (AddCommGroup W)) (inferInstanceAs (AddCommGroup M))
    (Submodule.module W) (inferInstanceAs (Module S M))
    P (originalDegreeVeroneseCoefficientChartScalarGraded B q) d f hf (f : S)
    (fun a : V => (a : S)) (originalDegreeVeroneseCoefficientDenominator B q f)
    (fun c => (originalDegreeVeroneseChartRingEquiv B q hf c).val)
    (originalDegreeVeroneseCoefficientLocalization B D hD q f)
    (originalDegreeVeroneseCoefficientScalarValue_mk B q hf)
    (originalDegreeVeroneseCoefficientLocalization_mk_smul B D hD q f)

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientLocalization_chart_smul
#print axioms LinearStudy.originalDegreeVeroneseCoefficientLocalization_chart_smul

