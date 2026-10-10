module
public import Linear.NormalizationWeightedSourceLinearMap
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
theorem nativeNormalizationWeightedSourceChartMap_bijective
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) :
    Function.Bijective (nativeNormalizationWeightedSourceChartMap 𝒜 𝓑 d a ha) := by
  letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
  constructor
  · intro x y h
    apply Subtype.ext
    apply (nativeNormalizationFullChartEquiv (S := S) a).injective
    calc
      nativeNormalizationFullChartEquiv (S := S) a x.val =
          (nativeNormalizationWeightedSourceChartMap 𝒜 𝓑 d a ha x).val :=
        (nativeNormalizationWeightedSourceChartMap_val 𝒜 𝓑 d a ha x).symm
      _ = (nativeNormalizationWeightedSourceChartMap 𝒜 𝓑 d a ha y).val := congrArg HomogeneousLocalization.val h
      _ = nativeNormalizationFullChartEquiv (S := S) a y.val :=
        nativeNormalizationWeightedSourceChartMap_val 𝒜 𝓑 d a ha y
  · intro z
    obtain ⟨x,hx⟩ := nativeNormalizationWeightedSourceAwayZero_surjective 𝒜 𝓑 d a ha z
    refine ⟨x,?_⟩
    apply HomogeneousLocalization.val_injective
    exact (nativeNormalizationWeightedSourceChartMap_val 𝒜 𝓑 d a ha x).trans hx

/-- A proved linear equivalence between the generated source chart module
and the complete ACTUAL homogeneous Proj chart of the original source. -/
def nativeNormalizationWeightedSourceChartEquiv (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) :
    nativeGradedModuleAwayDegreeZero 𝒜 (nativeProjectiveRingIntegerPiece 𝓑) d a ≃ₗ[HomogeneousLocalization.Away 𝒜 a]
      HomogeneousLocalization.Away 𝓑 (algebraMap R S a) :=
  LinearEquiv.ofBijective (nativeNormalizationWeightedSourceChartMap 𝒜 𝓑 d a ha)
    (nativeNormalizationWeightedSourceChartMap_bijective 𝒜 𝓑 d a ha)

/-- The equivalence is the original full-localization comparison, restricted
to degree zero. This prevents replacing the original chart by a supplied model. -/
theorem nativeNormalizationWeightedSourceChartEquiv_val
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) (x : nativeGradedModuleAwayDegreeZero 𝒜 (nativeProjectiveRingIntegerPiece 𝓑) d a) :
    (nativeNormalizationWeightedSourceChartEquiv 𝒜 𝓑 d a ha x).val =
      nativeNormalizationFullChartEquiv (S := S) a x.val :=
  nativeNormalizationWeightedSourceChartMap_val 𝒜 𝓑 d a ha x

end LinearStudy
