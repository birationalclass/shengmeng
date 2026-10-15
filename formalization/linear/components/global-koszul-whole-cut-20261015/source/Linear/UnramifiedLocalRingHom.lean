module
public import Linear.GenericUnramifiedOpen
public import Mathlib.RingTheory.Localization.AtPrime.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- Pointwise unramification suffices: no global unramification assumption is needed. -/
theorem ringHom_pointwiseUnramified_localRingHom
    {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (P : Ideal A) (Q : Ideal R)
    [P.IsPrime] [Q.IsPrime] (hQP : Q = P.comap φ)
    (hP : ((algebraMap A (Localization.AtPrime P)).comp φ).FormallyUnramified) :
    (Localization.localRingHom Q P φ hQP).FormallyUnramified := by
  have he : (Localization.localRingHom Q P φ hQP).comp
      (algebraMap R (Localization.AtPrime Q)) =
        (algebraMap A (Localization.AtPrime P)).comp φ := by
    apply RingHom.ext
    intro a
    exact Localization.localRingHom_to_map Q P φ hQP a
  rw [← he] at hP
  exact RingHom.FormallyUnramified.of_comp hP

theorem ringHom_formallyUnramified_localRingHom
    {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : φ.FormallyUnramified)
    (P : Ideal A) (Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hQP : Q = P.comap φ) :
    (Localization.localRingHom Q P φ hQP).FormallyUnramified := by
  have hl : (algebraMap A (Localization.AtPrime P)).FormallyUnramified :=
    RingHom.formallyUnramified_algebraMap.mpr
      (Algebra.FormallyUnramified.of_isLocalization P.primeCompl)
  have hc := hφ.comp hl
  have he : (Localization.localRingHom Q P φ hQP).comp
      (algebraMap R (Localization.AtPrime Q)) =
        (algebraMap A (Localization.AtPrime P)).comp φ := by
    apply RingHom.ext
    intro a
    exact Localization.localRingHom_to_map Q P φ hQP a
  rw [← he] at hc
  exact RingHom.FormallyUnramified.of_comp hc

theorem ringHom_essFiniteType_localRingHom
    {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : φ.EssFiniteType)
    (P : Ideal A) (Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hQP : Q = P.comap φ) :
    (Localization.localRingHom Q P φ hQP).EssFiniteType := by
  have hl : (algebraMap A (Localization.AtPrime P)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
  have hc := hφ.comp hl
  have he : (Localization.localRingHom Q P φ hQP).comp
      (algebraMap R (Localization.AtPrime Q)) =
        (algebraMap A (Localization.AtPrime P)).comp φ := by
    apply RingHom.ext
    intro a
    exact Localization.localRingHom_to_map Q P φ hQP a
  rw [← he] at hc
  exact RingHom.EssFiniteType.of_comp _ hc

end LinearStudy
