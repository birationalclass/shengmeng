module
public import Linear.NativeGlobalHomOriginalSectionEvaluation
public import Linear.ActualAffineHomSourceAction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- The SAME original global-to-affine Hom comparison preserves actual
source sections on the ORIGINAL degree-one chart. Compatibility follows
from original section evaluations and the original ring multiplication. -/
theorem nativeNormalizationGlobalAffineHomSections_original_source_action
    (a : R) (ha : a ∈ 𝒜 1)
    (b : HomogeneousLocalization.Away 𝓑 (algebraMap R S a))
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf), Proj.basicOpen 𝒜 a)) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let f := nativeNormalizationProjectiveMap 𝒜 𝓑
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    let Q : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha
      (schemePushforwardHomSourceActionSection f N (Proj.basicOpen 𝒜 a)
        ((Proj.awayToSection 𝓑 (algebraMap R S a)) b) h) =
      schemePushforwardHomSourceActionSection g Q ⊤
        (show Γ(Spec (CommRingCat.of B),g ⁻¹ᵁ ⊤) from
          (actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
            (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤ b))
        (nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha h) := by
  dsimp only
  let A := HomogeneousLocalization.Away 𝒜 a
  let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
  let f := nativeNormalizationProjectiveMap 𝒜 𝓑
  let U := Proj.basicOpen 𝒜 a
  let M := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
  let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let P := (Scheme.Modules.pushforward g).obj (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
  let Q : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  let e := Proj.basicOpenIsoSpec 𝒜 a ha (by decide)
  let hs := schemePushforwardHomSourceActionSection f N U
    ((Proj.awayToSection 𝓑 (algebraMap R S a)) b) h
  apply actualAffineAlgebraDualInternalHomSections_evaluation_ext (A := A) (B := B)
  intro x
  have hl := nativeNormalizationGlobalAffineHomSections_original_section_chart_pullback
    𝒜 𝓑 a ha hs x
  have hr := nativeNormalizationGlobalAffineHomSections_original_section_chart_pullback
    𝒜 𝓑 a ha h (b*x)
  have hm : schemeModuleHomSectionEvaluation M N U hs
      ((Proj.awayToSection 𝓑 (algebraMap R S a)) x) =
      schemeModuleHomSectionEvaluation M N U h
        ((Proj.awayToSection 𝓑 (algebraMap R S a)) (b*x)) := by
    rw [schemePushforwardHomSourceActionSection_original_evaluation]
    congr 1
    exact (map_mul (Proj.awayToSection 𝓑 (algebraMap R S a)).hom b x).symm
  have hf : schemeModuleHomSectionEvaluation P Q ⊤
      (schemePushforwardHomSourceActionSection g Q ⊤
        (show Γ(Spec (CommRingCat.of B),g ⁻¹ᵁ ⊤) from
          (actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
            (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤ b))
        (nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha h))
      ((actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
        (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤ x)) =
      schemeModuleHomSectionEvaluation P Q ⊤
        (nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha h)
        ((actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
          (tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤ (b*x))) := by
    rw [schemePushforwardHomSourceActionSection_original_evaluation,
      ← actualAffineAlgebraStructurePushforwardIso_element_mul]
  exact hl.trans ((congrArg (fun z => e.inv.appTop (U.topIso.inv z)) hm).trans
    (hr.symm.trans hf.symm))

end LinearStudy
