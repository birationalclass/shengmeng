module
public import Linear.OriginalDegreeVeroneseCoefficientChartDegree
public import Mathlib.Algebra.Module.LocalizedModule.Basic
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


/-- The powers used as chart denominators have the same values in S. -/
def originalDegreeVeroneseCoefficientDenominator (f : V) (s : Submonoid.powers f) :
    Submonoid.powers (f : S) :=
  ⟨((s : V) : S), by
    obtain ⟨n, hn⟩ := s.property
    exact ⟨n, congrArg (fun a : V => (a : S)) hn⟩⟩

omit [AddCommGroup M] [Module K M] [Module S M] in
theorem originalDegreeVeroneseCoefficientDenominator_surjective (f : V) :
    Function.Surjective (originalDegreeVeroneseCoefficientDenominator B q f) := by
  intro t
  obtain ⟨n, hn⟩ := t.property
  refine ⟨⟨f ^ n, ⟨n, rfl⟩⟩, Subtype.ext ?_⟩
  exact hn

/-- Send a coefficient fraction to its identical value in the original
localized coefficient module. -/
def originalDegreeVeroneseCoefficientLocalization (f : V)
    (z : LocalizedModule (Submonoid.powers f) W) :
    LocalizedModule (Submonoid.powers (f : S)) M :=
  LocalizedModule.liftOn z
    (fun p => LocalizedModule.mk (p.1 : M)
      (originalDegreeVeroneseCoefficientDenominator B q f p.2))
    (by
      intro p p' hp
      change LocalizedModule.r (Submonoid.powers f) W p p' at hp
      obtain ⟨u, hu⟩ := hp
      exact LocalizedModule.mk_eq.mpr
        ⟨originalDegreeVeroneseCoefficientDenominator B q f u,
          congrArg (fun x : W => (x : M)) hu⟩)

theorem originalDegreeVeroneseCoefficientLocalization_mk
    (f : V) (a : W) (s : Submonoid.powers f) :
    originalDegreeVeroneseCoefficientLocalization B D hD q f (LocalizedModule.mk a s) =
      LocalizedModule.mk (a : M) (originalDegreeVeroneseCoefficientDenominator B q f s) := rfl

theorem originalDegreeVeroneseCoefficientLocalization_injective (f : V) :
    Function.Injective (originalDegreeVeroneseCoefficientLocalization B D hD q f) := by
  intro x y
  refine LocalizedModule.induction_on₂ ?_ x y
  intro a a' s s' h
  rw [originalDegreeVeroneseCoefficientLocalization_mk,
      originalDegreeVeroneseCoefficientLocalization_mk] at h
  obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.mp h
  obtain ⟨u, rfl⟩ := originalDegreeVeroneseCoefficientDenominator_surjective B q f t
  exact LocalizedModule.mk_eq.mpr ⟨u, Subtype.ext ht⟩

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficientDenominator
#print axioms LinearStudy.originalDegreeVeroneseCoefficientDenominator
#check LinearStudy.originalDegreeVeroneseCoefficientDenominator_surjective
#print axioms LinearStudy.originalDegreeVeroneseCoefficientDenominator_surjective
#check LinearStudy.originalDegreeVeroneseCoefficientLocalization
#print axioms LinearStudy.originalDegreeVeroneseCoefficientLocalization
#check LinearStudy.originalDegreeVeroneseCoefficientLocalization_mk
#print axioms LinearStudy.originalDegreeVeroneseCoefficientLocalization_mk
#check LinearStudy.originalDegreeVeroneseCoefficientLocalization_injective
#print axioms LinearStudy.originalDegreeVeroneseCoefficientLocalization_injective

