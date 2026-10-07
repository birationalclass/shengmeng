module
public import Linear.SmoothRationalPoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Every nonempty principal open of an integral finite-type algebra
contains an actual smooth rational point. -/
theorem domain_exists_smooth_rational_point_avoiding
    {K A : Type*} [Field K] [IsAlgClosed K] [PerfectField K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FinitePresentation K A]
    (h : A) (hh : h ≠ 0) :
    ∃ ρ : A →ₐ[K] K, ρ h ≠ 0 ∧
      rationalPointPrime ρ ∈ Algebra.smoothLocus K A := by
  let B := Localization.Away h
  letI : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B
    (powers_le_nonZeroDivisors_of_noZeroDivisors hh)
  letI : Algebra.FinitePresentation A B := IsLocalization.Away.finitePresentation h
  letI : Algebra.FinitePresentation K B := Algebra.FinitePresentation.trans K A B
  obtain ⟨_, φ, _, _, hp⟩ := domain_exists_smooth_rational_point (K := K) (A := B)
  let ρ := φ.comp (IsScalarTower.toAlgHom K A B)
  have hu : ρ h ≠ 0 := isUnit_iff_ne_zero.mp
    ((IsLocalization.Away.algebraMap_isUnit h (S := B)).map φ)
  have hpA : PrimeSpectrum.comap (algebraMap A B) (rationalPointPrime φ) ∈
      Algebra.smoothLocus K A := by
    have he := congrArg (fun S : Set (PrimeSpectrum B) => rationalPointPrime φ ∈ S)
      (Algebra.smoothLocus_comap_of_isLocalization (R := K) (Af := B) h)
    exact he.mpr hp
  have he : PrimeSpectrum.comap (algebraMap A B) (rationalPointPrime φ) =
      rationalPointPrime ρ := by
    apply PrimeSpectrum.ext
    change (RingHom.ker φ.toRingHom).comap (algebraMap A B) = RingHom.ker ρ.toRingHom
    rw [RingHom.comap_ker]
    rfl
  exact ⟨ρ, hu, he ▸ hpA⟩

end LinearStudy
