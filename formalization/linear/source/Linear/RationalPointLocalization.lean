module
public import Linear.SmoothRationalPoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

theorem rationalPointPrime_away_comap
    {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    (a : B) (ρ : Localization.Away a →ₐ[K] K) :
    PrimeSpectrum.comap (algebraMap B (Localization.Away a)) (rationalPointPrime ρ) =
      rationalPointPrime (ρ.comp (IsScalarTower.toAlgHom K B (Localization.Away a))) := by
  apply PrimeSpectrum.ext
  change (RingHom.ker ρ.toRingHom).comap (algebraMap B (Localization.Away a)) = _
  rw [RingHom.comap_ker]
  rfl

/-- Smoothness of the actual open-chart point is smoothness of the same base point. -/
theorem rationalPoint_away_smooth_base
    {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    (a : B) (ρ : Localization.Away a →ₐ[K] K)
    (hρ : rationalPointPrime ρ ∈ Algebra.smoothLocus K (Localization.Away a)) :
    rationalPointPrime (ρ.comp (IsScalarTower.toAlgHom K B (Localization.Away a))) ∈
      Algebra.smoothLocus K B := by
  have h := congrArg (fun S : Set (PrimeSpectrum (Localization.Away a)) =>
      rationalPointPrime ρ ∈ S)
    (Algebra.smoothLocus_comap_of_isLocalization (R := K) (Af := Localization.Away a) a)
  have hh := h.mpr hρ
  change PrimeSpectrum.comap (algebraMap B (Localization.Away a)) (rationalPointPrime ρ) ∈
    Algebra.smoothLocus K B at hh
  rwa [rationalPointPrime_away_comap] at hh

theorem rationalPoint_away_denominator_ne_zero
    {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    (a : B) (ρ : Localization.Away a →ₐ[K] K) :
    ρ (algebraMap B (Localization.Away a) a) ≠ 0 :=
  isUnit_iff_ne_zero.mp ((IsLocalization.Away.algebraMap_isUnit a).map ρ)

theorem rationalPoint_away_invSelf
    {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    (a : B) (ρ : Localization.Away a →ₐ[K] K) :
    ρ (IsLocalization.Away.invSelf a) =
      (ρ (algebraMap B (Localization.Away a) a))⁻¹ := by
  have hn := rationalPoint_away_denominator_ne_zero a ρ
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn]
  have h := congrArg ρ (IsLocalization.Away.mul_invSelf (S := Localization.Away a) a)
  simpa only [map_mul, map_one] using h

end LinearStudy
