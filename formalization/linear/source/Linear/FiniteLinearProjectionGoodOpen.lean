module
public import Linear.ProjectiveLinearNormalization
public import Linear.GenericSmoothUnramifiedOpen
public import Linear.TargetGoodLoci
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Localization.Integral
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy

/-- Generic unramification is derived from a finite injective map in
characteristic zero, rather than assumed for the projection. -/
theorem finite_injective_algHom_fraction_comp_formallyUnramified
    {K R A : Type*} [Field K] [CharZero K]
    [CommRing R] [IsDomain R] [Algebra K R]
    [CommRing A] [IsDomain A] [Algebra K A]
    (φ : R →ₐ[K] A) (hinj : Function.Injective φ) (hfinite : φ.Finite) :
    ((algebraMap A (FractionRing A)).comp φ.toRingHom).FormallyUnramified := by
  let F := FractionRing R
  let L := FractionRing A
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : Module.Finite R A := hfinite
  let ψ : R →ₐ[K] L := (IsScalarTower.toAlgHom K A L).comp φ
  have hψ : Function.Injective ψ := (IsFractionRing.injective A L).comp hinj
  let χ : F →ₐ[K] L := IsFractionRing.liftAlgHom (K := F) hψ
  have hχR (r : R) : χ (algebraMap R F r) = ψ r :=
    IsFractionRing.lift_algebraMap hψ r
  letI : Algebra F L := χ.toRingHom.toAlgebra
  letI : SMul R F := (inferInstance : Algebra R F).toSMul
  letI : Algebra R L := ψ.toRingHom.toAlgebra
  letI : SMul R L := ψ.toRingHom.toAlgebra.toSMul
  letI : Module R L := Algebra.toModule
  letI : Module.IsTorsionFree R L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hψ
  letI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq
    (R := R) (S := A) (A := L) (fun _ => rfl)
  letI : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq
    (R := R) (S := F) (A := L) (fun r => (IsFractionRing.lift_algebraMap hψ r).symm)
  letI : Algebra.IsAlgebraic R A := inferInstance
  letI : Algebra.IsAlgebraic R L :=
    (IsFractionRing.isAlgebraic_iff' R A L).mp inferInstance
  letI : Algebra.IsAlgebraic F L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := F) (C := L)).mp
      (inferInstance : Algebra.IsAlgebraic R L)
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  letI : Algebra.FormallyUnramified F L := Algebra.FormallyUnramified.of_isSeparable F L
  have hχ : χ.toRingHom.FormallyUnramified := RingHom.formallyUnramified_algebraMap.mpr
    (inferInstance : Algebra.FormallyUnramified F L)
  have hFR : (algebraMap R F).FormallyUnramified := RingHom.formallyUnramified_algebraMap.mpr
    (Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors R))
  have he : χ.toRingHom.comp (algebraMap R F) =
      (algebraMap A L).comp φ.toRingHom := by
    apply RingHom.ext
    intro r
    exact hχR r
  have hc : (χ.toRingHom.comp (algebraMap R F)).FormallyUnramified :=
    RingHom.FormallyUnramified.comp (f := algebraMap R F) (g := χ.toRingHom) hFR hχ
  exact he ▸ hc

/-- A genuine finite dominant projection has a nonempty target open
whose entire preimage is smooth and unramified for that same map. -/
theorem finite_injective_algHom_exists_target_good_loci
    {K R A : Type*} [Field K] [CharZero K]
    [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FinitePresentation K R]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FinitePresentation K A]
    (φ : R →ₐ[K] A) (hinj : Function.Injective φ) (hfinite : φ.Finite) :
    letI : Algebra R A := φ.toRingHom.toAlgebra
    ∃ c : R, c ≠ 0 ∧ φ c ≠ 0 ∧ ∀ P : PrimeSpectrum A,
      φ c ∉ P.asIdeal → P ∈ Algebra.smoothLocus K A ∧
        PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus K R ∧
        P ∈ Algebra.unramifiedLocus R A := by
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : Module.Finite R A := hfinite
  have hft : φ.toRingHom.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.mpr inferInstance
  obtain ⟨a,ha,hs,hu⟩ := ringHom_fractionModel_exists_smooth_unramified_open
    (K := K) (L := FractionRing A) φ.toRingHom hft
      (finite_injective_algHom_fraction_comp_formallyUnramified φ hinj hfinite)
  exact injective_algebraic_map_exists_target_good_loci φ hinj inferInstance a ha hs hu

/-- In addition, the WHOLE inverse image of that same target open
avoids any specified proper principal closed subset of the source. -/
theorem finite_injective_algHom_exists_target_good_loci_avoiding
    {K R A : Type*} [Field K] [CharZero K]
    [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FinitePresentation K R]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FinitePresentation K A]
    (φ : R →ₐ[K] A) (hinj : Function.Injective φ) (hfinite : φ.Finite)
    (a : A) (ha : a ≠ 0) :
    letI : Algebra R A := φ.toRingHom.toAlgebra
    ∃ c : R, c ≠ 0 ∧ φ c ≠ 0 ∧ ∀ P : PrimeSpectrum A,
      φ c ∉ P.asIdeal → a ∉ P.asIdeal ∧ P ∈ Algebra.smoothLocus K A ∧
        PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus K R ∧
        P ∈ Algebra.unramifiedLocus R A := by
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : Module.Finite R A := hfinite
  obtain ⟨c,hc,hφc,hgood⟩ := finite_injective_algHom_exists_target_good_loci φ hinj hfinite
  obtain ⟨b,hb,havoid⟩ := ringHom_algebraic_target_open_avoids_source_closed
    φ.toRingHom inferInstance a ha
  have hcb : c*b ≠ 0 := mul_ne_zero hc hb
  refine ⟨c*b,hcb,fun hz => hcb (hinj (by simpa using hz)),?_⟩
  intro P hP
  have hcP : φ c ∉ P.asIdeal := by
    intro h
    apply hP
    rw [map_mul]
    exact P.asIdeal.mul_mem_right _ h
  have hbP : φ b ∉ P.asIdeal := by
    intro h
    apply hP
    rw [map_mul]
    exact P.asIdeal.mul_mem_left _ h
  exact ⟨havoid P hbP,hgood P hcP⟩

end LinearStudy
