module
public import Linear.NativeOriginalGlobalAffineHomSourceAction
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

/-- The SAME original global native comparison recovers the SAME
original affine comparison after the SAME global-to-affine Hom chart. -/
theorem nativeDualGlobalHomChartLinearEquiv_original_affine_roundtrip
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha
      (nativeDualGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinj ell) =
      nativeAffineInternalHomSectionsLinearEquiv 𝒜 𝓑 a ha hinj ell := by
  let A := HomogeneousLocalization.Away 𝒜 a
  let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let P := (Scheme.Modules.pushforward g).obj
    (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
  let Q : (Spec (CommRingCat.of A)).Modules :=
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  letI := nativeNormalizationGlobalHomChartModule 𝒜 𝓑 a ha
  letI := originalAffineHomBaseModule (CommRingCat.of A) P Q
  dsimp only [nativeDualGlobalHomChartLinearEquiv]
  exact (nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha).apply_symm_apply _
end LinearStudy
