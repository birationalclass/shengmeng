module
public import Linear.GoodRationalPointForMap
public import Linear.UnramifiedLocalRingHom
public import Linear.UnramifiedParameters
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

theorem rationalPointPrime_comp_comap
    {K R A : Type*} [Field K] [CommRing R] [CommRing A]
    [Algebra K R] [Algebra K A] (φ : R →ₐ[K] A) (ρ : A →ₐ[K] K) :
    (rationalPointPrime (ρ.comp φ)).asIdeal = (rationalPointPrime ρ).asIdeal.comap φ.toRingHom := by
  change RingHom.ker (ρ.comp φ).toRingHom = (RingHom.ker ρ.toRingHom).comap φ.toRingHom
  rw [RingHom.comap_ker]
  rfl

/-- The actual local map at a rational point and its image. -/
def rationalPointLocalMap
    {K R A : Type*} [Field K] [CommRing R] [CommRing A]
    [Algebra K R] [Algebra K A] (φ : R →ₐ[K] A) (ρ : A →ₐ[K] K) :
    Localization.AtPrime (rationalPointPrime (ρ.comp φ)).asIdeal →+*
      Localization.AtPrime (rationalPointPrime ρ).asIdeal :=
  Localization.localRingHom _ _ φ.toRingHom (rationalPointPrime_comp_comap φ ρ)

theorem rationalPointLocalMap_essFiniteType
    {K R A : Type*} [Field K] [CommRing R] [CommRing A]
    [Algebra K R] [Algebra K A] (φ : R →ₐ[K] A) (ρ : A →ₐ[K] K)
    (hφ : φ.toRingHom.EssFiniteType) : (rationalPointLocalMap φ ρ).EssFiniteType :=
  ringHom_essFiniteType_localRingHom φ.toRingHom hφ _ _ (rationalPointPrime_comp_comap φ ρ)

theorem rationalPointLocalMap_formallyUnramified
    {K R A : Type*} [Field K] [CommRing R] [CommRing A]
    [Algebra K R] [Algebra K A] (φ : R →ₐ[K] A) (ρ : A →ₐ[K] K)
    (hρ : letI : Algebra R A := φ.toRingHom.toAlgebra
      rationalPointPrime ρ ∈ Algebra.unramifiedLocus R A) :
    (rationalPointLocalMap φ ρ).FormallyUnramified := by
  letI : Algebra R A := φ.toRingHom.toAlgebra
  have hP : Algebra.IsUnramifiedAt R (rationalPointPrime ρ).asIdeal := hρ
  have hcomp : ((algebraMap A (Localization.AtPrime (rationalPointPrime ρ).asIdeal)).comp
      φ.toRingHom).FormallyUnramified := RingHom.formallyUnramified_algebraMap.mpr hP
  exact ringHom_pointwiseUnramified_localRingHom φ.toRingHom _ _
    (rationalPointPrime_comp_comap φ ρ) hcomp

/-- Actual local pullbacks of any target maximal-ideal generators generate the source ideal. -/
theorem rationalPointLocalMap_parameters_generate
    {K R A ι : Type*} [Field K] [CommRing R] [CommRing A]
    [Algebra K R] [Algebra K A] (φ : R →ₐ[K] A) (ρ : A →ₐ[K] K)
    (hφ : φ.toRingHom.EssFiniteType)
    (hρ : letI : Algebra R A := φ.toRingHom.toAlgebra
      rationalPointPrime ρ ∈ Algebra.unramifiedLocus R A)
    (t : ι → Localization.AtPrime (rationalPointPrime (ρ.comp φ)).asIdeal)
    (ht : Ideal.span (Set.range t) =
      IsLocalRing.maximalIdeal (Localization.AtPrime (rationalPointPrime (ρ.comp φ)).asIdeal)) :
    Ideal.span (Set.range (fun i => rationalPointLocalMap φ ρ (t i))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime (rationalPointPrime ρ).asIdeal) := by
  let B := Localization.AtPrime (rationalPointPrime (ρ.comp φ)).asIdeal
  let C := Localization.AtPrime (rationalPointPrime ρ).asIdeal
  letI : Algebra B C := (rationalPointLocalMap φ ρ).toAlgebra
  letI : IsLocalHom (algebraMap B C) := Localization.isLocalHom_localRingHom
    (rationalPointPrime (ρ.comp φ)).asIdeal (rationalPointPrime ρ).asIdeal
      φ.toRingHom (rationalPointPrime_comp_comap φ ρ)
  letI : Algebra.EssFiniteType B C := RingHom.essFiniteType_algebraMap.mp
    (rationalPointLocalMap_essFiniteType φ ρ hφ)
  letI : Algebra.FormallyUnramified B C := RingHom.formallyUnramified_algebraMap.mp
    (rationalPointLocalMap_formallyUnramified φ ρ hρ)
  exact unramified_local_parameters_generate (S := C) t ht

end LinearStudy
