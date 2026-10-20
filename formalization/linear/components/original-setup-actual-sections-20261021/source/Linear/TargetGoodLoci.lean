module
public import Linear.FractionModelAlgebraicOpen
public import Linear.GoodRationalPointForMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Algebraicity moves a source good open to the target; intersecting with the
target smooth open makes all preimages and images good, with a nonempty pullback. -/
theorem injective_algebraic_map_exists_target_good_loci
    {K R A : Type*} [Field K] [PerfectField K]
    [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra K R] [Algebra K A]
    [Algebra.FinitePresentation K R] [Algebra.FinitePresentation K A]
    (φ : R →ₐ[K] A) (hφ : Function.Injective φ)
    (halg : letI : Algebra R A := φ.toRingHom.toAlgebra; Algebra.IsAlgebraic R A)
    (a : A) (ha : a ≠ 0) (hs : Algebra.Smooth K (Localization.Away a))
    (hu : ((algebraMap A (Localization.Away a)).comp φ.toRingHom).FormallyUnramified) :
    letI : Algebra R A := φ.toRingHom.toAlgebra
    ∃ c : R, c ≠ 0 ∧ φ c ≠ 0 ∧ ∀ P : PrimeSpectrum A,
      φ c ∉ P.asIdeal → P ∈ Algebra.smoothLocus K A ∧
        PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus K R ∧
        P ∈ Algebra.unramifiedLocus R A := by
  letI : Algebra R A := φ.toRingHom.toAlgebra
  obtain ⟨b, hb, hab⟩ := ringHom_algebraic_target_open_avoids_source_closed
    φ.toRingHom halg a ha
  obtain ⟨u, hu0, hus⟩ := domain_exists_nonzero_smooth_basic_open (K := K) (A := R)
  have hsrc : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) ⊆
      Algebra.smoothLocus K A := Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hs
  have htgt : (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum R)) ⊆
      Algebra.smoothLocus K R := Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hus
  have hu' : (algebraMap R (Localization.Away a)).FormallyUnramified := hu
  have hunram : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) ⊆
      Algebra.unramifiedLocus R A := Algebra.basicOpen_subset_unramifiedLocus_iff.mpr
        (RingHom.formallyUnramified_algebraMap.mp hu')
  have hc : b * u ≠ 0 := mul_ne_zero hb hu0
  refine ⟨b * u, hc, fun hz => hc (hφ (by simpa using hz)), ?_⟩
  intro P hPc
  have hbP : φ b ∉ P.asIdeal := by
    intro hbP
    apply hPc
    rw [map_mul]
    exact P.asIdeal.mul_mem_right _ hbP
  have huP : φ u ∉ P.asIdeal := by
    intro huP
    apply hPc
    rw [map_mul]
    exact P.asIdeal.mul_mem_left _ huP
  have haP : P ∈ PrimeSpectrum.basicOpen a := hab P hbP
  have huQ : PrimeSpectrum.comap φ.toRingHom P ∈ PrimeSpectrum.basicOpen u := huP
  exact ⟨hsrc haP, htgt huQ, hunram haP⟩

end LinearStudy
