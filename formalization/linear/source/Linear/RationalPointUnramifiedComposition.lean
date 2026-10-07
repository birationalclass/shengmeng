module
public import Linear.RationalPointLocalMap
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

theorem rationalPointPrime_comp_formallyUnramified
    {K R A : Type*} [Field K] [CommRing R] [CommRing A]
    [Algebra K R] [Algebra K A] (φ : R →ₐ[K] A) (ρ : A →ₐ[K] K)
    (hρ : letI : Algebra R A := φ.toRingHom.toAlgebra
      rationalPointPrime ρ ∈ Algebra.unramifiedLocus R A) :
    ((algebraMap A (Localization.AtPrime (rationalPointPrime ρ).asIdeal)).comp
      φ.toRingHom).FormallyUnramified := by
  letI : Algebra R A := φ.toRingHom.toAlgebra
  have hP : Algebra.IsUnramifiedAt R (rationalPointPrime ρ).asIdeal := hρ
  exact RingHom.formallyUnramified_algebraMap.mpr hP

end LinearStudy
