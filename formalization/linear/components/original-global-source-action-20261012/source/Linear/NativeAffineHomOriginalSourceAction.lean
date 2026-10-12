module
public import Linear.NativeFullChartOriginalSourceAction
public import Linear.ActualAffineHomSourceAction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The ORIGINAL native affine chart comparison is the specified
actual affine internal-Hom comparison of the ORIGINAL chart functional.
No comparison or scalar-compatibility certificate is supplied. -/
theorem nativeAffineInternalHomSectionsEquiv_original_chart_functional
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj ell =
      actualAffineAlgebraDualInternalHomSectionsLinearEquiv
        (A := HomogeneousLocalization.Away 𝒜 a)
        (B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
        (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj ell) := by
  rfl

/-- On the ACTUAL original affine homogeneous chart, the SAME original
native dual comparison preserves the ACTUAL source-section action
on the ORIGINAL internal-Hom sheaf. -/
theorem nativeAffineInternalHomSectionsEquiv_original_source_action
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (b : HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
    (ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj
      ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm
        (b • nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha ell)) =
      schemePushforwardHomSourceActionSection g
        (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf) ⊤
        (show Γ(Spec (CommRingCat.of B),g ⁻¹ᵁ ⊤) from
          (actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
            (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤ b))
        (nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj ell) := by
  dsimp only
  rw [nativeAffineInternalHomSectionsEquiv_original_chart_functional,
    nativeAffineInternalHomSectionsEquiv_original_chart_functional]
  apply actualAffineAlgebraDualInternalHomSections_evaluation_ext
  intro x
  rw [actualAffineAlgebraDualInternalHomSectionsLinearEquiv_spec_value,
    schemePushforwardHomSourceActionSection_original_evaluation,
    ← actualAffineAlgebraStructurePushforwardIso_element_mul,
    actualAffineAlgebraDualInternalHomSectionsLinearEquiv_spec_value,
    finiteNativeDualFullSourceChartMap_original_source_action]
  rw [mul_comm x b]

end LinearStudy
