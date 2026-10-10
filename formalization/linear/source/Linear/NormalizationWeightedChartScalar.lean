module
public import Linear.NormalizationSourceChartLinearMap
public import Linear.NativeGradedModuleOverlapDegree
public import Linear.NativeProjectiveRingIntegerPieces
public import Linear.NativeNormalizationFullChartComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization

/-- The actual normalization chart map on arbitrary homogeneous degrees. -/
theorem normalizationHomogeneousWeightedChartMap_mk
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) (n : ℕ) (x : R) (hx : x ∈ 𝒜 (n*d)) :
    (normalizationHomogeneousChartMap 𝒜 𝓑 a
      (HomogeneousLocalization.Away.mk 𝒜 ha n x
        (by simpa only [smul_eq_mul] using hx))).val =
      IsLocalization.mk' (M := Submonoid.powers (algebraMap R S a))
        (Localization.Away (algebraMap R S a)) (algebraMap R S x)
        ⟨(algebraMap R S a)^n,
          (Submonoid.powers (algebraMap R S a)).pow_mem (Submonoid.mem_powers _) n⟩ := by
  exact (congrArg HomogeneousLocalization.val
    (HomogeneousLocalization.Away.map_mk (normalizationBaseGradedRingHom 𝒜 𝓑)
      a ha n x (by simpa only [smul_eq_mul] using hx))).trans
    (Localization.mk_eq_mk'_apply _ _)

/-- The full original source localization comparison preserves the
ACTUAL homogeneous base-chart scalar action. -/
theorem nativeNormalizationFullChartEquiv_weighted_chart_smul
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d)
    (c : HomogeneousLocalization.Away 𝒜 a)
    (x : LocalizedModule (Submonoid.powers a) S) :
    nativeNormalizationFullChartEquiv (S := S) a (c • x) =
      (normalizationHomogeneousChartMap 𝒜 𝓑 a c).val *
        nativeNormalizationFullChartEquiv (S := S) a x := by
  let Q := Localization.Away a
  letI : Module Q (LocalizedModule (Submonoid.powers a) S) :=
    LocalizedModule.moduleOfIsLocalization
  obtain ⟨n,c,hc,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ha c
  induction x using LocalizedModule.induction_on with
  | _ b s =>
      have hc' : c ∈ 𝒜 (n*d) := by simpa only [smul_eq_mul, mul_one] using hc
      with_unfolding_all
        change nativeNormalizationFullChartEquiv (S := S) a
          (algebraMap (HomogeneousLocalization.Away 𝒜 a) Q
            (HomogeneousLocalization.Away.mk 𝒜 ha n c hc) • LocalizedModule.mk b s) = _
      rw [← localizedModule_abstract_smul_eq_native (Submonoid.powers a)]
      rw [HomogeneousLocalization.algebraMap_apply,
        HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
        LocalizedModule.mk'_smul_mk Q, nativeNormalizationFullChartEquiv_mk]
      rw [normalizationHomogeneousWeightedChartMap_mk 𝒜 𝓑 d a ha n c hc',
        nativeNormalizationFullChartEquiv_mk,
        ← IsLocalization.mk'_mul]
      congr 1
      · exact Algebra.smul_def c b
      · apply Subtype.ext
        simp only [Submonoid.coe_mul, map_mul, map_pow]

end LinearStudy
