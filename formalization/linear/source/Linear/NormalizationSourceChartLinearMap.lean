module
public import Linear.NormalizationSourceChartSurjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization

/-- The original source chart is an algebra over the original normalization
chart via its actual homogeneous chart map. -/
@[instance_reducible] def normalizationHomogeneousSourceChartAlgebra (a : R) :
    Algebra (HomogeneousLocalization.Away 𝒜 a)
      (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :=
  (normalizationHomogeneousChartMap 𝒜 𝓑 a).toAlgebra

attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- The actual full-localization comparison restricts to a base-chart linear
map from the ORIGINAL generated source chart to the full native Proj chart. -/
def nativeNormalizationSourceChartMap (a : R) (ha : a ∈ 𝒜 1) :
    nativeNormalizationSourceAwayZero 𝒜 𝓑 a →ₗ[HomogeneousLocalization.Away 𝒜 a]
      HomogeneousLocalization.Away 𝓑 (algebraMap R S a) := by
  let g := fun x : nativeNormalizationSourceAwayZero 𝒜 𝓑 a =>
    (nativeNormalizationSourceAwayZero_value 𝒜 𝓑 a ha x.val x.property).choose
  have hg (x : nativeNormalizationSourceAwayZero 𝒜 𝓑 a) :
      (g x).val = nativeNormalizationFullChartEquiv (S := S) a x.val :=
    (nativeNormalizationSourceAwayZero_value 𝒜 𝓑 a ha x.val x.property).choose_spec
  exact {
    toFun := g
    map_add' := by
      intro x y
      apply HomogeneousLocalization.val_injective
      rw [hg,HomogeneousLocalization.val_add,hg,hg]
      exact (nativeNormalizationFullChartEquiv (S := S) a).map_add x.val y.val
    map_smul' := by
      intro c x
      apply HomogeneousLocalization.val_injective
      change (g (c • x)).val = (c • g x).val
      rw [hg,Algebra.smul_def,HomogeneousLocalization.val_mul,hg]
      exact nativeNormalizationFullChartEquiv_chart_smul 𝒜 𝓑 a ha c x.val }

/-- The restricted map retains the actual original localization value. -/
theorem nativeNormalizationSourceChartMap_val (a : R) (ha : a ∈ 𝒜 1)
    (x : nativeNormalizationSourceAwayZero 𝒜 𝓑 a) :
    (nativeNormalizationSourceChartMap 𝒜 𝓑 a ha x).val =
      nativeNormalizationFullChartEquiv (S := S) a x.val :=
  (nativeNormalizationSourceAwayZero_value 𝒜 𝓑 a ha x.val x.property).choose_spec

end LinearStudy
