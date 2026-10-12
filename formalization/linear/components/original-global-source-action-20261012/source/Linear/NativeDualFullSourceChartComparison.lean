module
public import Linear.NormalizationSourceChartEquiv
public import Linear.NativeDualDegreeZeroChartInjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- Compare the original degree-zero dual with linear functionals on the
FULL ACTUAL original source Proj chart, using the proved source equivalence.
This construction does not yet assert surjectivity or canonical identification. -/
def finiteNativeDualFullSourceChartMap
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a
      →ₗ[HomogeneousLocalization.Away 𝒜 a]
        (HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
          →ₗ[HomogeneousLocalization.Away 𝒜 a] HomogeneousLocalization.Away 𝒜 a) := by
  let A₀ := HomogeneousLocalization.Away 𝒜 a
  let B₀ := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let X₀ := nativeNormalizationSourceAwayZero 𝒜 𝓑 a
  let E := nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha
  let pre : (X₀ →ₗ[A₀] A₀) →ₗ[A₀] (B₀ →ₗ[A₀] A₀) := {
    toFun := fun f => f.comp E.symm.toLinearMap
    map_add' := by intro f g; ext b; rfl
    map_smul' := by intro c f; ext b; rfl }
  exact pre.comp (finiteNativeDualDegreeZeroChartMap 𝒜 𝓑 a ha hinj)

/-- Values are still the original native-localization evaluation, at the
actual inverse image of the source-chart fraction. -/
theorem finiteNativeDualFullSourceChartMap_apply_val
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a)
    (y : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell y).val =
      finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away a)
        (Submonoid.powers a) hinj ell.val
        ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm y).val := by
  exact finiteNativeDualDegreeZeroChartMap_apply 𝒜 𝓑 a ha hinj ell
    ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm y)

/-- The dual comparison remains injective on the FULL actual source chart,
rather than just the previously generated source submodule. -/
theorem finiteNativeDualFullSourceChartMap_injective
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    Function.Injective (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj) := by
  intro ell₁ ell₂ h
  apply finiteNativeDualDegreeZeroChartMap_injective 𝒜 𝓑 a ha hinj
  ext x
  have hx := congrArg (fun f => f (nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha x)) h
  change finiteNativeDualDegreeZeroChartMap 𝒜 𝓑 a ha hinj ell₁
      ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm
        (nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha x)) =
    finiteNativeDualDegreeZeroChartMap 𝒜 𝓑 a ha hinj ell₂
      ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm
        (nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha x)) at hx
  simpa only [LinearEquiv.symm_apply_apply] using congrArg HomogeneousLocalization.val hx

end LinearStudy
