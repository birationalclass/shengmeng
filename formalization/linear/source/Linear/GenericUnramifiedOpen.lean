module
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.Localization.FractionRing
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- Spread actual nonramification at the generic point to a nonempty
principal open in the target spectrum of the ring map. -/
theorem ringHom_genericPoint_exists_nonzero_unramified_open
    {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    (φ : R →+* A) (hft : φ.EssFiniteType)
    (hg : ((algebraMap A (Localization.AtPrime (⊥ : Ideal A))).comp φ).FormallyUnramified) :
    ∃ a : A, a ≠ 0 ∧
      ((algebraMap A (Localization.Away a)).comp φ).FormallyUnramified := by
  letI : Algebra R A := φ.toAlgebra
  letI : Algebra.EssFiniteType R A := hft
  have hg' : (algebraMap R (Localization.AtPrime (⊥ : Ideal A))).FormallyUnramified := hg
  letI : Algebra.IsUnramifiedAt R (⊥ : Ideal A) :=
    RingHom.formallyUnramified_algebraMap.mp hg'
  obtain ⟨a, ha, hu⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := R) (⊥ : Ideal A)
  refine ⟨a, by simpa using ha, ?_⟩
  exact RingHom.formallyUnramified_algebraMap.mpr hu

/-- The actual fraction-ring map gives the generic local-ring property;
no independent generic-point nonramification input is added. -/
theorem ringHom_fraction_exists_nonzero_unramified_open
    {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    (φ : R →+* A) (hft : φ.EssFiniteType)
    (hg : ((algebraMap A (FractionRing A)).comp φ).FormallyUnramified) :
    ∃ a : A, a ≠ 0 ∧
      ((algebraMap A (Localization.Away a)).comp φ).FormallyUnramified := by
  let B := Localization.AtPrime (⊥ : Ideal A)
  letI : IsFractionRing A B := by
    simpa only [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization (⊥ : Ideal A).primeCompl B)
  let e := IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A) B
  have he : e.toRingHom.FormallyUnramified :=
    RingHom.FormallyUnramified.of_surjective e.surjective
  have hc := hg.comp he
  have hi : e.toRingHom.comp ((algebraMap A (FractionRing A)).comp φ) =
      (algebraMap A B).comp φ := by
    apply RingHom.ext
    intro x
    exact e.commutes (φ x)
  rw [hi] at hc
  exact ringHom_genericPoint_exists_nonzero_unramified_open φ hft hc

end LinearStudy
