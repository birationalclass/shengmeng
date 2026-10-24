module
public import Linear.SmoothPointPrincipalOpen
public import Linear.GenericUnramifiedOpen
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Choose a genuine rational point which is smooth, unramified for the given
map, and whose image is also smooth. All three conditions hold at one point. -/
theorem injectiveMap_exists_smooth_unramified_rational_point
    {K R A : Type*} [Field K] [IsAlgClosed K] [PerfectField K]
    [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra K R] [Algebra K A]
    [Algebra.FinitePresentation K R] [Algebra.FinitePresentation K A]
    (φ : R →ₐ[K] A) (hφ : Function.Injective φ)
    (b : A) (hb : b ≠ 0)
    (hU : ((algebraMap A (Localization.Away b)).comp φ.toRingHom).FormallyUnramified) :
    letI : Algebra R A := φ.toRingHom.toAlgebra
    ∃ ρ : A →ₐ[K] K,
      rationalPointPrime ρ ∈ Algebra.smoothLocus K A ∧
      rationalPointPrime (ρ.comp φ) ∈ Algebra.smoothLocus K R ∧
      rationalPointPrime ρ ∈ Algebra.unramifiedLocus R A := by
  letI : Algebra R A := φ.toRingHom.toAlgebra
  obtain ⟨u, hu, hs⟩ := domain_exists_nonzero_smooth_basic_open (K := K) (A := R)
  have hpu : φ u ≠ 0 := fun hz => hu (hφ (by simpa using hz))
  obtain ⟨ρ, hρ, hsource⟩ := domain_exists_smooth_rational_point_avoiding
    (K := K) (A := A) (b * φ u) (mul_ne_zero hb hpu)
  rw [map_mul] at hρ
  have hρb := (mul_ne_zero_iff.mp hρ).1
  have hρu := (mul_ne_zero_iff.mp hρ).2
  have ht : (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum R)) ⊆ Algebra.smoothLocus K R :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hs
  have hu' : rationalPointPrime (ρ.comp φ) ∈ PrimeSpectrum.basicOpen u := by
    change (ρ.comp φ) u ≠ 0
    exact hρu
  have hU' : (algebraMap R (Localization.Away b)).FormallyUnramified := hU
  have hgood : (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum A)) ⊆
      Algebra.unramifiedLocus R A := Algebra.basicOpen_subset_unramifiedLocus_iff.mpr
        (RingHom.formallyUnramified_algebraMap.mp hU')
  have hb' : rationalPointPrime ρ ∈ PrimeSpectrum.basicOpen b := by
    change ρ b ≠ 0
    exact hρb
  exact ⟨ρ, hsource, ht hu', hgood hb'⟩

end LinearStudy
