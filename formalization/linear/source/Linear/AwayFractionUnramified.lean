module
public import Linear.AwayFractionEmbedding
public import Mathlib.RingTheory.Localization.LocalizationLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- Spread generic nonramification using any actual fraction-field model. -/
theorem ringHom_fractionModel_exists_nonzero_unramified_open
    {R A L : Type*} [CommRing R] [CommRing A] [IsDomain A] [Field L]
    [Algebra A L] [IsFractionRing A L]
    (φ : R →+* A) (hft : φ.EssFiniteType)
    (hg : ((algebraMap A L).comp φ).FormallyUnramified) :
    ∃ a : A, a ≠ 0 ∧
      ((algebraMap A (Localization.Away a)).comp φ).FormallyUnramified := by
  let B := Localization.AtPrime (⊥ : Ideal A)
  letI : IsFractionRing A B := by
    simpa only [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization (⊥ : Ideal A).primeCompl B)
  let e := IsLocalization.algEquiv (nonZeroDivisors A) L B
  have he : e.toRingHom.FormallyUnramified :=
    RingHom.FormallyUnramified.of_surjective e.surjective
  have hc := hg.comp he
  have hi : e.toRingHom.comp ((algebraMap A L).comp φ) =
      (algebraMap A B).comp φ := by
    apply RingHom.ext
    intro x
    exact e.commutes (φ x)
  rw [hi] at hc
  exact ringHom_genericPoint_exists_nonzero_unramified_open φ hft hc

/-- The denominator chart is a domain with the same actual fraction field. -/
theorem awayFractionEmbedding_exists_unramified_open
    {K R B : Type*} [Field K] [CommRing R] [CommRing B] [IsDomain B] [Algebra K B]
    (a : B) (ha : a ≠ 0) (φ : R →+* Localization.Away a) (hft : φ.EssFiniteType)
    (hg : ((awayFractionEmbedding (K := K) a ha).toRingHom.comp φ).FormallyUnramified) :
    ∃ b : Localization.Away a, b ≠ 0 ∧
      ((algebraMap (Localization.Away a) (Localization.Away b)).comp φ).FormallyUnramified := by
  let A := Localization.Away a
  let L := FractionRing B
  letI : IsDomain A := Localization.Away.isDomain ha
  letI : Algebra A L := (awayFractionEmbedding (K := K) a ha).toRingHom.toAlgebra
  letI : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq
    (fun b => (awayFractionEmbedding_algebraMap (K := K) a ha b).symm)
  letI : IsFractionRing A L := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers a) A L
  exact ringHom_fractionModel_exists_nonzero_unramified_open (L := L) φ hft hg

end LinearStudy
