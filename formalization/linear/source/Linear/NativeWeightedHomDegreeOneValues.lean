module
public import Linear.ActualAffineAlgebraDualInternalHomValues
public import Linear.NativeDualGlobalHomWeightedOverlapLinear
public import Linear.NativeNormalizationGlobalWeightedAffineHomLinear
public import Linear.NativeNormalizationWeightedOverlapDualEquiv
public import Linear.NativeDualFullSourceChartEquiv
public import Linear.NativeDualGlobalHomChartLinear
public import Linear.CoextensionBaseGradeCompatibility
public import Linear.NormalizationHomogeneousAffineDualOverlapLocalization
public import Mathlib.Algebra.Module.Torsion.Pi
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  normalizationHomogeneousSourceChartAlgebra

theorem nativeNormalizationGlobalWeightedHom_degree_one_value
    (a : R) (ha : a ∈ 𝒜 1)
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf), Proj.basicOpen 𝒜 a)) :
    nativeNormalizationGlobalWeightedAffineHomSectionsLinearEquiv 𝒜 𝓑 1
      (by decide) a ha h = nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha h := by
  rfl

theorem nativeDualGlobalHomChartLinearEquiv_affine_section_value
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    nativeNormalizationGlobalWeightedAffineHomSectionsLinearEquiv 𝒜 𝓑 1 (by decide) a ha
      (nativeDualGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj ell) =
      actualAffineAlgebraDualInternalHomSectionsLinearEquiv
        (A := HomogeneousLocalization.Away 𝒜 a)
        (B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
        (finiteNativeDualFullSourceChartEquiv 𝒜 𝓑 a ha hinj ell) := by
  rw [nativeNormalizationGlobalWeightedHom_degree_one_value]
  simp only [nativeDualGlobalHomChartLinearEquiv, id_eq,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  exact (congr($(actualAffineAlgebraDualInternalHomSectionsLinearEquiv_eq_native
    𝒜 𝓑 a ha hinj) ell)).symm
end LinearStudy
