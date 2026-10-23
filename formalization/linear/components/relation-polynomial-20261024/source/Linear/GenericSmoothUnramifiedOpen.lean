module
public import Linear.GenericSmoothOpen
public import Linear.GenericUnramifiedOpen
public import Linear.AwayFractionUnramified
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

/-- A single nonempty principal open can be smooth over the ground field
and unramified for the given map at the same time. -/
theorem domain_exists_nonzero_smooth_unramified_open
    {K R A : Type*} [Field K] [PerfectField K] [CommRing R] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FinitePresentation K A] [Algebra R A] [Algebra.EssFiniteType R A]
    [Algebra.IsUnramifiedAt R (⊥ : Ideal A)] :
    ∃ a : A, a ≠ 0 ∧ Algebra.Smooth K (Localization.Away a) ∧
      Algebra.FormallyUnramified R (Localization.Away a) := by
  let F := Localization.AtPrime (⊥ : Ideal A)
  letI : IsFractionRing A F := by
    simpa only [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization (⊥ : Ideal A).primeCompl F)
  letI : Field F := IsFractionRing.toField A
  letI : Algebra.EssFiniteType A F :=
    Algebra.EssFiniteType.of_isLocalization F (⊥ : Ideal A).primeCompl
  letI : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K A F
  letI : Algebra.IsSmoothAt K (⊥ : Ideal A) := inferInstance
  let p : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  have hp : p ∈ Algebra.smoothLocus K A ∩ Algebra.unramifiedLocus R A := by
    constructor
    · exact (inferInstance : Algebra.IsSmoothAt K (⊥ : Ideal A))
    · exact (inferInstance : Algebra.IsUnramifiedAt R (⊥ : Ideal A))
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hpa, ha⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp
      ((Algebra.isOpen_smoothLocus (R := K) (A := A)).inter
        (Algebra.isOpen_unramifiedLocus (R := R) (A := A)))
  refine ⟨a, by simpa [p] using hpa, ?_, ?_⟩
  · apply Algebra.basicOpen_subset_smoothLocus_iff_smooth.mp
    exact fun q hq => (ha hq).1
  · apply Algebra.basicOpen_subset_unramifiedLocus_iff.mp
    exact fun q hq => (ha hq).2

/-- Generic information from an actual fraction-field model gives a common
smooth and unramified principal open for a ring map. -/
theorem ringHom_fractionModel_exists_smooth_unramified_open
    {K R A L : Type*} [Field K] [PerfectField K] [CommRing R] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FinitePresentation K A] [Field L] [Algebra A L] [IsFractionRing A L]
    (φ : R →+* A) (hft : φ.EssFiniteType)
    (hg : ((algebraMap A L).comp φ).FormallyUnramified) :
    ∃ a : A, a ≠ 0 ∧ Algebra.Smooth K (Localization.Away a) ∧
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
  letI : Algebra R A := φ.toAlgebra
  letI : Algebra.EssFiniteType R A := hft
  have hg' : (algebraMap R B).FormallyUnramified := hc
  letI : Algebra.IsUnramifiedAt R (⊥ : Ideal A) :=
    RingHom.formallyUnramified_algebraMap.mp hg'
  obtain ⟨a, ha, hs, hu⟩ := domain_exists_nonzero_smooth_unramified_open (K := K) (R := R) (A := A)
  exact ⟨a, ha, hs, RingHom.formallyUnramified_algebraMap.mpr hu⟩

end LinearStudy
