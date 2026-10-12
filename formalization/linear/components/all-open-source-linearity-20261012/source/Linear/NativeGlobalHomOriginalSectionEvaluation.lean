module
public import Linear.SchemeModuleHomAffineTransportLinear
public import Linear.NativeNormalizationPushforwardStructureChart
public import Linear.OriginalProjectiveChartScalarTransport
public import Linear.SchemeModuleHomTransportedEvaluation
public import Linear.NativeNormalizationOriginalSourceElementValue
public import Linear.NativeNormalizationGlobalAffineHomLinear
public import Linear.NativeGlobalHomOriginalElementEvaluation
public import Linear.SchemeModuleCompositeTopEvaluation
public import Linear.StructureUnitChartTopValue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra
theorem nativeNormalizationGlobalAffineHomSections_original_section_evaluation
    (a : R) (ha : a ∈ 𝒜 1)
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf), Proj.basicOpen 𝒜 a))
    (x : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let U := Proj.basicOpen 𝒜 a
    let e := Proj.basicOpenIsoSpec 𝒜 a ha (by decide)
    let M := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    let P := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    let Q : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    let β := Scheme.Modules.restrictUnitIso (Proj.awayι 𝒜 a ha (by decide))
    let y := M.presheaf.map (eqToHom
      (show Proj.awayι 𝒜 a ha (by decide) ''ᵁ ⊤ = U by
        simp [U, Proj.awayι, Scheme.Hom.comp_image, Scheme.Hom.image_top_eq_opensRange,
          Scheme.Hom.opensRange_of_isIso, Scheme.Opens.ι_image_top])).op
        ((Proj.awayToSection 𝓑 (algebraMap R S a)) x)
    schemeModuleHomSectionEvaluation P Q ⊤
      (nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha h)
      ((actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
        ((tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤) x)) =
      β.hom.app ⊤ (N.presheaf.map (eqToHom
        (show Proj.awayι 𝒜 a ha (by decide) ''ᵁ ⊤ = U by
          simp [U, Proj.awayι, Scheme.Hom.comp_image,
            Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso])).op
        (schemeModuleHomSectionEvaluation M N U h
          ((Proj.awayToSection 𝓑 (algebraMap R S a)) x))) := by
  dsimp only
  have h1 := nativeNormalizationGlobalAffineHomSections_original_element_evaluation
    𝒜 𝓑 a ha h x
  have h2 := schemeModuleHomCompositeRestriction_top_evaluation
    ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf)
    (Proj.basicOpen 𝒜 a) (Proj.basicOpenIsoSpec 𝒜 a ha (by decide)).inv h
    ((Proj.awayToSection 𝓑 (algebraMap R S a)) x)
  exact h1.trans (congrArg
    (fun z => (Scheme.Modules.restrictUnitIso (Proj.awayι 𝒜 a ha (by decide))).hom.app ⊤ z) h2)
theorem nativeNormalizationGlobalAffineHomSections_original_section_chart_pullback
    (a : R) (ha : a ∈ 𝒜 1)
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
        (SheafOfModules.unit (Proj 𝓑).ringCatSheaf))
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf), Proj.basicOpen 𝒜 a))
    (x : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    let A := HomogeneousLocalization.Away 𝒜 a
    let B := HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
    let U := Proj.basicOpen 𝒜 a
    let e := Proj.basicOpenIsoSpec 𝒜 a ha (by decide)
    let M := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
      (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
    let N : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
    let P := (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
    let Q : (Spec (CommRingCat.of A)).Modules := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
    let β := Scheme.Modules.restrictUnitIso (Proj.awayι 𝒜 a ha (by decide))
    let y := M.presheaf.map (eqToHom
      (show Proj.awayι 𝒜 a ha (by decide) ''ᵁ ⊤ = U by
        simp [U, Proj.awayι, Scheme.Hom.comp_image, Scheme.Hom.image_top_eq_opensRange,
          Scheme.Hom.opensRange_of_isIso, Scheme.Opens.ι_image_top])).op
        ((Proj.awayToSection 𝓑 (algebraMap R S a)) x)
    schemeModuleHomSectionEvaluation P Q ⊤
      (nativeNormalizationGlobalAffineHomSectionsLinearEquiv 𝒜 𝓑 a ha h)
      ((actualAffineAlgebraStructurePushforwardIso (A := A) (B := B)).hom.app ⊤
        ((tilde.toOpen (R := CommRingCat.of A) (ModuleCat.of A B) ⊤) x)) =
      e.inv.appTop (U.topIso.inv
        (schemeModuleHomSectionEvaluation M N U h
          ((Proj.awayToSection 𝓑 (algebraMap R S a)) x))) := by
  dsimp only
  have h1 := nativeNormalizationGlobalAffineHomSections_original_section_evaluation
    𝒜 𝓑 a ha h x
  have h2 := structureUnitChartTopValue (Proj.basicOpen 𝒜 a)
    (Proj.basicOpenIsoSpec 𝒜 a ha (by decide))
    (schemeModuleHomSectionEvaluation _ _ (Proj.basicOpen 𝒜 a) h
      ((Proj.awayToSection 𝓑 (algebraMap R S a)) x))
  exact h1.trans (eq_of_heq h2)
end LinearStudy
