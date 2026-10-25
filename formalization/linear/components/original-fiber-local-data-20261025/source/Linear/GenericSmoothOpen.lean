module
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Localization.FractionRing
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- An integral finitely presented algebra over a perfect field has a
nonempty smooth principal open, derived from its actual generic point. -/
theorem domain_exists_nonzero_smooth_basic_open
    {K A : Type*} [Field K] [PerfectField K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FinitePresentation K A] :
    ∃ a : A, a ≠ 0 ∧ Algebra.Smooth K (Localization.Away a) := by
  let F := Localization.AtPrime (⊥ : Ideal A)
  letI : IsFractionRing A F := by
    simpa only [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization (⊥ : Ideal A).primeCompl F)
  letI : Field F := IsFractionRing.toField A
  letI : Algebra.EssFiniteType A F :=
    Algebra.EssFiniteType.of_isLocalization F (⊥ : Ideal A).primeCompl
  letI : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K A F
  letI : Algebra.IsSmoothAt K (⊥ : Ideal A) := inferInstance
  obtain ⟨a, ha, hs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth K (⊥ : Ideal A)
  exact ⟨a, by simpa using ha, hs⟩

end LinearStudy
