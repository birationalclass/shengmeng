module
public import Linear.NativeAffineHomOriginalSourceAction
public import Linear.ActualAffineNativeDualSourceLinear
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

/-- The ORIGINAL native base/source zero-chart comparison is additive. -/
theorem nativeCoextensionBaseSourceZeroChartEquiv_add
    (a : R) (ha : a ∈ 𝒜 1)
    (ell k : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a) :
    nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha (ell+k) =
      nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha ell +
        nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha k := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  apply Subtype.ext
  exact _root_.map_add (moduleBaseSourceLocalizationEquiv (S := S) a) ell.val k.val

/-- Its ORIGINAL inverse is additive on actual source-chart elements. -/
theorem nativeCoextensionBaseSourceZeroChartEquiv_symm_add
    (a : R) (ha : a ∈ 𝒜 1)
    (d e : nativeGradedModuleAwayZero 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (algebraMap R S a)) :
    (nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm (d+e) =
      (nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm d +
        (nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm e := by
  apply (nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).injective
  rw [nativeCoextensionBaseSourceZeroChartEquiv_add,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The source-native chart to actual Hom comparison preserves the
original source-section action, with its source-native domain. -/
theorem nativeAffineInternalHomSectionsEquiv_native_source_action
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (b : HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
    (d : nativeGradedModuleAwayZero 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (algebraMap R S a)) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj
      ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm (b • d)) =
      schemePushforwardHomSourceActionSection g
        (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf) ⊤
        (show Γ(Spec (CommRingCat.of B),g ⁻¹ᵁ ⊤) from
          (actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
            (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤ b))
        (nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj
          ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm d)) := by
  simpa only [Equiv.apply_symm_apply] using
    nativeAffineInternalHomSectionsEquiv_original_source_action 𝒜 𝓑 a ha hinj b
      ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm d)

/-- The SAME explicit original native source Proj-chart comparison is
an actual B0-LINEAR equivalence to the ORIGINAL affine internal Hom,
whose B0 action comes from actual source sections. It is not a
canonical-dualizing identification or a supplied scalar certificate. -/
def nativeAffineOriginalSourceChartHomLinearEquiv
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let H := Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward g).obj
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf),⊤)
    letI : Module B H := actualAffineOriginalHomSourceModule (A := A) (B := B)
    nativeGradedModuleAwayZero 𝓑 (coextensionGradedPiece 𝒜 𝓑) (algebraMap R S a) ≃ₗ[B] H := by
  dsimp only
  let A := HomogeneousLocalization.Away 𝒜 a
  let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let H := Γ(schemeModuleHomModuleSheaf
    ((Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
    (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf),⊤)
  letI : Module B H := actualAffineOriginalHomSourceModule (A := A) (B := B)
  let E := (nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm.trans
    (nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj)
  refine { __ := E, map_add' := ?_, map_smul' := ?_ }
  · intro d e
    change nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj
        ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm (d+e)) =
      nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj
        ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm d) +
      nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj
        ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm e)
    rw [nativeCoextensionBaseSourceZeroChartEquiv_symm_add,
      nativeAffineInternalHomSectionsEquiv_add]
  · intro b d
    change nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj
        ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm (b • d)) =
      schemePushforwardHomSourceActionSection g
        (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf) ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
        (nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj
          ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm d))
    have hb := eq_of_heq
      (actualAffineAlgebraStructurePushforwardIso_element_value (A := A) b)
    have hs := nativeAffineInternalHomSectionsEquiv_native_source_action 𝒜 𝓑 a ha hinj b d
    dsimp only at hs
    rw [hb] at hs
    exact hs

/-- The B0-linear equivalence retains the SAME original chart map. -/
theorem nativeAffineOriginalSourceChartHomLinearEquiv_apply
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (d : nativeGradedModuleAwayZero 𝓑 (coextensionGradedPiece 𝒜 𝓑)
      (algebraMap R S a)) :
    nativeAffineOriginalSourceChartHomLinearEquiv 𝒜 𝓑 a ha hinj d =
      nativeAffineInternalHomSectionsEquiv 𝒜 𝓑 a ha hinj
        ((nativeCoextensionBaseSourceZeroChartEquiv 𝒜 𝓑 a ha).symm d) := rfl

end LinearStudy
