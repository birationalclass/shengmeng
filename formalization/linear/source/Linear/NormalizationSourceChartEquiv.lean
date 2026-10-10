module
public import Linear.NormalizationSourceChartLinearMap
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
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The original generated source chart is exactly the full original native
degree-zero chart: the comparison is bijective, not only injective. -/
theorem nativeNormalizationSourceChartMap_bijective
    (a : R) (ha : a ∈ 𝒜 1) :
    Function.Bijective (nativeNormalizationSourceChartMap 𝒜 𝓑 a ha) := by
  letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
  constructor
  · intro x y h
    apply Subtype.ext
    apply (nativeNormalizationFullChartEquiv (S := S) a).injective
    calc
      nativeNormalizationFullChartEquiv (S := S) a x.val =
          (nativeNormalizationSourceChartMap 𝒜 𝓑 a ha x).val :=
        (nativeNormalizationSourceChartMap_val 𝒜 𝓑 a ha x).symm
      _ = (nativeNormalizationSourceChartMap 𝒜 𝓑 a ha y).val := congrArg HomogeneousLocalization.val h
      _ = nativeNormalizationFullChartEquiv (S := S) a y.val :=
        nativeNormalizationSourceChartMap_val 𝒜 𝓑 a ha y
  · intro z
    obtain ⟨x,hx⟩ := nativeNormalizationSourceAwayZero_surjective 𝒜 𝓑 a ha z
    refine ⟨x,?_⟩
    apply HomogeneousLocalization.val_injective
    exact (nativeNormalizationSourceChartMap_val 𝒜 𝓑 a ha x).trans hx

/-- A proved linear equivalence between the generated source chart module
and the complete ACTUAL homogeneous Proj chart of the original source. -/
def nativeNormalizationSourceChartEquiv (a : R) (ha : a ∈ 𝒜 1) :
    nativeNormalizationSourceAwayZero 𝒜 𝓑 a ≃ₗ[HomogeneousLocalization.Away 𝒜 a]
      HomogeneousLocalization.Away 𝓑 (algebraMap R S a) :=
  LinearEquiv.ofBijective (nativeNormalizationSourceChartMap 𝒜 𝓑 a ha)
    (nativeNormalizationSourceChartMap_bijective 𝒜 𝓑 a ha)

/-- The equivalence is the original full-localization comparison, restricted
to degree zero. This prevents replacing the original chart by a supplied model. -/
theorem nativeNormalizationSourceChartEquiv_val
    (a : R) (ha : a ∈ 𝒜 1) (x : nativeNormalizationSourceAwayZero 𝒜 𝓑 a) :
    (nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha x).val =
      nativeNormalizationFullChartEquiv (S := S) a x.val :=
  nativeNormalizationSourceChartMap_val 𝒜 𝓑 a ha x

end LinearStudy
