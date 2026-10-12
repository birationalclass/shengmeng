module
public import Linear.NativeDualHomogeneousEvaluationMap
public import Mathlib.Algebra.Module.Submodule.Equiv
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
attribute [local instance] nativeCoextensionNormalizationBaseModule
attribute [local instance] LocalizedModule.moduleOfIsLocalization
attribute [local instance] nativeHomogeneousAwayModuleScalar

/-- Construct a map from the actual degree-zero native normalization
dual to the linear dual of the actual degree-zero source chart module.
This is a map, not a claimed equivalence or canonical-sheaf identification. -/
def finiteNativeDualDegreeZeroChartMap
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a
      →ₗ[HomogeneousLocalization.Away 𝒜 a]
        (nativeNormalizationSourceAwayZero 𝒜 𝓑 a
          →ₗ[HomogeneousLocalization.Away 𝒜 a] HomogeneousLocalization.Away 𝒜 a) := by
  let A₀ := HomogeneousLocalization.Away 𝒜 a
  let Q := Localization.Away a
  let D₀ := nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a
  let X₀ := nativeNormalizationSourceAwayZero 𝒜 𝓑 a
  let H := finiteNativeDualHomogeneousEvaluationMap (S := S) 𝒜 a hinj
  let H₀ := (LinearMap.domRestrict' X₀).comp (H.domRestrict D₀)
  let j := Algebra.linearMap A₀ Q
  have hj : Function.Injective j := HomogeneousLocalization.val_injective (Submonoid.powers a)
  have hrange : ∀ ell : D₀, ∀ x : X₀, H₀ ell x ∈ j.range := by
    intro ell x
    exact finiteNativeDual_degreeZero_span_value 𝒜 𝓑 a ha hinj ell.val ell.property
      x.val x.property
  exact LinearMap.codRestrict₂ H₀ j hj hrange

/-- The chart map is the ORIGINAL native localization evaluation, with
values in the actual homogeneous chart ring. -/
theorem finiteNativeDualDegreeZeroChartMap_apply
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a)
    (x : nativeNormalizationSourceAwayZero 𝒜 𝓑 a) :
    (finiteNativeDualDegreeZeroChartMap 𝒜 𝓑 a ha hinj ell x).val =
      finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away a)
        (Submonoid.powers a) hinj ell.val x.val := by
  unfold finiteNativeDualDegreeZeroChartMap
  exact LinearMap.codRestrict₂_apply
    ((LinearMap.domRestrict' (nativeNormalizationSourceAwayZero 𝒜 𝓑 a)).comp
      ((finiteNativeDualHomogeneousEvaluationMap (S := S) 𝒜 a hinj).domRestrict
        (nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a)))
    (Algebra.linearMap (HomogeneousLocalization.Away 𝒜 a) (Localization.Away a))
    (HomogeneousLocalization.val_injective (Submonoid.powers a))
    (fun ell x => finiteNativeDual_degreeZero_span_value 𝒜 𝓑 a ha hinj
      ell.val ell.property x.val x.property) ell x

end LinearStudy
