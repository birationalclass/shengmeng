module
public import Linear.NativeOriginalGlobalAffineHomSourceAction
public import Linear.NativeGlobalHomOriginalAffineRoundtrip
public import Linear.NativeAffineSourceChartHomLinear
public import Linear.NativeDualGlobalHomChartLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 150000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- Source multiplication for the SAME original global native dual
comparison follows from its original affine roundtrip. No alternative
comparison or supplied source-compatibility certificate is introduced. -/
theorem nativeDualGlobalHomChartLinearEquiv_original_source_action
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (b : HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
    (d : nativeGradedModuleAwayZero 𝓑 (coextensionGradedPiece 𝒜 𝓑) (algebraMap R S a)) :
    nativeDualGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj
      ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm (b • d)) =
      schemePushforwardHomSourceActionSection (nativeNormalizationProjectiveMap 𝒜 𝓑)
        (SheafOfModules.unit (Proj 𝒜).ringCatSheaf) (Proj.basicOpen 𝒜 a)
        ((Proj.awayToSection 𝓑 (algebraMap R S a)) b)
        (nativeDualGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj
          ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm d)) := by
  let A := HomogeneousLocalization.Away 𝒜 a
  let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let P := (Scheme.Modules.pushforward g).obj
    (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
  let Q : (Spec (CommRingCat.of A)).Modules :=
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 a ha
  letI := originalAffineHomBaseModule (CommRingCat.of A) P Q
  apply (nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha).injective
  rw [nativeDualGlobalHomChartLinearEquiv_original_affine_roundtrip]
  have hs := nativeNormalizationGlobalAffineHomSections_original_source_action 𝒜 𝓑 a ha b
    (nativeDualGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj
      ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm d))
  dsimp only at hs
  rw [hs,nativeDualGlobalHomChartLinearEquiv_original_affine_roundtrip]
  exact nativeAffineInternalHomSectionsEquiv_native_source_action 𝒜 𝓑 a ha hinj b d
end LinearStudy
