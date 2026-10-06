module
public import Linear.ParameterLinearPart
public import Linear.PowerSeriesCoefficients
public import Linear.PowerSeriesRegular
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Noetherian.Basic

/-! Actual formal parameter automorphisms, constructed from maximal-ideal generators using adic completeness and Noetherian kernel stabilization. This does not construct the action of arbitrary lifted parameters on the thickened equation quotient. -/
@[expose] public section
noncomputable section
namespace LinearStudy

theorem noetherian_ringEnd_injective_of_surjective
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (f : R →+* R) (hf : Function.Surjective f) : Function.Injective f := by
  let kernels : ℕ →o Submodule R R :=
    { toFun := fun n => RingHom.ker (f ^ n)
      monotone' := monotone_nat_of_le_succ (by
        intro n x hx
        change (f ^ (n + 1)) x = 0
        change (f ^ n) x = 0 at hx
        simp only [RingHom.coe_pow, Function.iterate_succ_apply'] at *
        rw [hx, map_zero]) }
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance kernels
  have hzero (x : R) (hx : f x = 0) : x = 0 := by
    obtain ⟨y, hy⟩ := hf.iterate n x
    have hnext : y ∈ kernels (n + 1) := by
      change (f ^ (n + 1)) y = 0
      simp only [RingHom.coe_pow, Function.iterate_succ_apply']
      rw [hy, hx]
    rw [← hn (n + 1) (Nat.le_succ n)] at hnext
    change (f ^ n) y = 0 at hnext
    simpa only [RingHom.coe_pow, hy] using hnext
  intro a b hab
  exact sub_eq_zero.mp (hzero (a - b) (by rw [map_sub, hab, sub_self]))

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem powerSeries_coordinateIdeal_eq_maximalIdeal :
    Ideal.span (Set.range (MvPowerSeries.X (R := K) (σ := ι))) =
      IsLocalRing.maximalIdeal (MvPowerSeries ι K) := by
  rw [← powerSeries_constantCoeff_kernel]
  ext f
  change f.constantCoeff = 0 ↔ ¬ IsUnit f
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  simp

omit [Nonempty ι] in
theorem parameter_substitution_hasSubst
    (T : ι → MvPowerSeries ι K)
    (hT : Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries ι K)) :
    MvPowerSeries.HasSubst T where
  const_coeff i := by rw [parameter_generator_constantCoeff_zero T hT i]; exact IsNilpotent.zero
  coeff_zero _ := Set.toFinite _

theorem parameter_substitution_surjective
    (T : ι → MvPowerSeries ι K)
    (hT : Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries ι K)) :
    Function.Surjective (MvPowerSeries.substAlgHom (R := K) (parameter_substitution_hasSubst T hT)) := by
  let I : Ideal (MvPowerSeries ι K) := Ideal.span (Set.range MvPowerSeries.X)
  let f := (MvPowerSeries.substAlgHom (R := K) (parameter_substitution_hasSubst T hT)).toRingHom
  have hmap : I.map f = I := by
    rw [Ideal.map_span, ← Set.range_comp]
    have heq : (f ∘ MvPowerSeries.X) = T := by
      funext i
      exact MvPowerSeries.substAlgHom_X _ i
    rw [heq, hT]
    exact powerSeries_coordinateIdeal_eq_maximalIdeal.symm
  have : IsHausdorff (I.map f) (MvPowerSeries ι K) := by rw [hmap]; infer_instance
  apply surjective_of_mk_map_comp_surjective (I := I) f
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨MvPowerSeries.C a.constantCoeff, ?_⟩
  change Ideal.Quotient.mk (I.map f) (f (MvPowerSeries.C a.constantCoeff)) = _
  have hc : f (MvPowerSeries.C a.constantCoeff) = MvPowerSeries.C a.constantCoeff := by
    exact (MvPowerSeries.substAlgHom (R := K) (parameter_substitution_hasSubst T hT)).commutes _
  rw [hc, Ideal.Quotient.eq, hmap]
  change MvPowerSeries.C a.constantCoeff - a ∈ Ideal.span (Set.range MvPowerSeries.X)
  rw [← powerSeries_constantCoeff_kernel]
  change (MvPowerSeries.C a.constantCoeff - a).constantCoeff = 0
  simp

theorem parameter_substitution_bijective
    (T : ι → MvPowerSeries ι K)
    (hT : Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries ι K)) :
    Function.Bijective (MvPowerSeries.substAlgHom (R := K) (parameter_substitution_hasSubst T hT)) :=
  ⟨noetherian_ringEnd_injective_of_surjective _ (parameter_substitution_surjective T hT),
    parameter_substitution_surjective T hT⟩

def parameterSubstitutionEquiv
    (T : ι → MvPowerSeries ι K)
    (hT : Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries ι K)) :
    MvPowerSeries ι K ≃ₐ[K] MvPowerSeries ι K :=
  AlgEquiv.ofBijective (MvPowerSeries.substAlgHom (R := K) (parameter_substitution_hasSubst T hT))
    (parameter_substitution_bijective T hT)

theorem parameterSubstitutionEquiv_X
    (T : ι → MvPowerSeries ι K)
    (hT : Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries ι K)) (i : ι) :
    parameterSubstitutionEquiv T hT (MvPowerSeries.X i) = T i :=
  MvPowerSeries.substAlgHom_X (parameter_substitution_hasSubst T hT) i

theorem parameterSubstitutionEquiv_symm_T
    (T : ι → MvPowerSeries ι K)
    (hT : Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries ι K)) (i : ι) :
    (parameterSubstitutionEquiv T hT).symm (T i) = MvPowerSeries.X i := by
  rw [← parameterSubstitutionEquiv_X T hT i, AlgEquiv.symm_apply_apply]

theorem powerSeries_parameter_generators_regular
    {r : ℕ} (hr : 0 < r) (T : Fin r → MvPowerSeries (Fin r) K)
    (hT : Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K)) :
    RingTheory.Sequence.IsRegular (MvPowerSeries (Fin r) K) (List.ofFn T) := by
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have h := (regular_transport_ringEquiv (parameterSubstitutionEquiv T hT).toRingEquiv _).mp
    (powerSeries_variables_regular (R := K) r)
  rw [List.map_ofFn] at h
  have heq : ((parameterSubstitutionEquiv T hT).toRingEquiv ∘ MvPowerSeries.X) = T := by
    funext i
    exact parameterSubstitutionEquiv_X T hT i
  rwa [heq] at h

end LinearStudy
