module
public import Linear.NativeCoextensionBaseSourceCharts
public import Linear.NativeDualFullSourceChartComparison
public import Linear.NativeDualSourceChangedAction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The inverse of the SAME original source-chart map has the value
of the inverse of the SAME full localization comparison. -/
theorem nativeNormalizationSourceChartEquiv_symm_val
    (a : R) (ha : a ∈ 𝒜 1)
    (y : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
    ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm y).val =
      (nativeNormalizationFullChartEquiv (S := S) a).symm y.val := by
  letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
  apply (nativeNormalizationFullChartEquiv (S := S) a).injective
  rw [AlgEquiv.apply_symm_apply]
  calc
    nativeNormalizationFullChartEquiv (S := S) a
        ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm y).val =
      (nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha
        ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm y)).val :=
      (nativeNormalizationSourceChartEquiv_val 𝒜 𝓑 a ha _).symm
    _ = y.val := congrArg HomogeneousLocalization.val
      ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).apply_symm_apply y)

/-- Multiplication by an ACTUAL homogeneous source-chart scalar is
the original full-localization multiplication after the chart inverse. -/
theorem nativeNormalizationSourceChartEquiv_symm_mul_val
    (a : R) (ha : a ∈ 𝒜 1)
    (y b : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
    ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm (y*b)).val =
      ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm y).val *
        (nativeNormalizationFullChartEquiv (S := S) a).symm b.val := by
  letI := nativeLocalizedUpperAlgebra (S := S) (Submonoid.powers a)
  rw [nativeNormalizationSourceChartEquiv_symm_val,
    nativeNormalizationSourceChartEquiv_symm_val]
  simpa only [HomogeneousLocalization.val_mul] using
    _root_.map_mul (nativeNormalizationFullChartEquiv (S := S) a).symm y.val b.val

variable [Module.Finite R S]

/-- The inverse of the original native degree-zero dual chart comparison
is the original universal localization inverse on values. -/
theorem nativeCoextensionBaseSourceZeroChartEquiv_symm_val
    (a : R) (ha : a ∈ 𝒜 1)
    (y : nativeGradedModuleAwayZero 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (algebraMap R S a)) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
    ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm y).val =
      (moduleBaseSourceLocalizationEquiv (S := S) a).symm y.val := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  apply (moduleBaseSourceLocalizationEquiv (S := S) a).injective
  rw [LinearEquiv.apply_symm_apply]
  calc
    moduleBaseSourceLocalizationEquiv (S := S) a
        ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm y).val =
      (nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha
        ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm y)).val :=
      (nativeCoextensionBaseSourceZeroChartEquiv_apply 𝒜 𝓑 a ha _).symm
    _ = y.val := congrArg Subtype.val
      ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).apply_symm_apply y)

end LinearStudy
