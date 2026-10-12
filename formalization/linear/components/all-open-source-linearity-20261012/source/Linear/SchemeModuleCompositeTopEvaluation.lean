module
public import Linear.SchemeModuleHomCompositeEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
variable (f : Y ⟶ (U : Scheme)) [IsOpenImmersion f]
theorem schemeModuleCompositeSectionsTransport_value (W : Y.Opens)
    (x : Γ(M,U.ι ''ᵁ (f ''ᵁ W))) :
    ((Scheme.Modules.restrictFunctorComp f U.ι).symm.app M).hom.app W
      (((M.restrict U.ι).restrictAppIso f W).inv
        ((M.restrictAppIso U.ι (f ''ᵁ W)).inv x)) =
    M.presheaf.map (eqToHom (show (f ≫ U.ι) ''ᵁ W = U.ι ''ᵁ (f ''ᵁ W) by
      simp [Scheme.Hom.comp_image])).op x := by
  rfl

attribute [local irreducible] schemeModuleHomCompositeRestriction
theorem schemeModuleHomCompositeRestriction_top_evaluation [IsIso f]
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) (r : Γ(M,U)) :
    (schemeModuleHomCompositeRestriction M N U f h).app ⊤
      (M.presheaf.map (eqToHom (show (f ≫ U.ι) ''ᵁ ⊤ = U by
        simp [Scheme.Hom.comp_image, Scheme.Hom.image_top_eq_opensRange,
          Scheme.Hom.opensRange_of_isIso, Scheme.Opens.ι_image_top])).op r) =
    N.presheaf.map (eqToHom (show (f ≫ U.ι) ''ᵁ ⊤ = U by
      simp [Scheme.Hom.comp_image, Scheme.Hom.image_top_eq_opensRange,
        Scheme.Hom.opensRange_of_isIso, Scheme.Opens.ι_image_top])).op
      (schemeModuleHomSectionEvaluation M N U h r) := by
  let V := U.ι ''ᵁ (f ''ᵁ ⊤)
  let i : V ⟶ U := homOfLE
    ((Scheme.Hom.image_mono U.ι le_top).trans (le_of_eq U.ι_image_top))
  have hv := schemeModuleHomCompositeRestriction_evaluation M N U f h ⊤
    (M.presheaf.map i.op r)
  dsimp only at hv
  have hx := schemeModuleCompositeSectionsTransport_value M U f ⊤ (M.presheaf.map i.op r)
  have hy := schemeModuleCompositeSectionsTransport_value N U f ⊤
    (schemeModuleHomSectionEvaluation M N V
      ((schemeModuleHomModuleSheaf M N).presheaf.map i.op h) (M.presheaf.map i.op r))
  have hm := (congrArg (fun z =>
    (schemeModuleHomCompositeRestriction M N U f h).app ⊤ z) hx.symm).trans hv
  have hv' := hm.trans hy
  have hr := schemeModuleHomSectionEvaluation_restrict M N i h r
  have hn := congrArg (fun z => N.presheaf.map
    (eqToHom (show (f ≫ U.ι) ''ᵁ ⊤ = U.ι ''ᵁ (f ''ᵁ ⊤) by
      simp [Scheme.Hom.comp_image])).op z) hr
  have hall := hv'.trans hn
  have hmap (P : X.Modules) (z : Γ(P,U)) :
      P.presheaf.map (eqToHom (show (f ≫ U.ι) ''ᵁ ⊤ = U by
        simp [Scheme.Hom.comp_image, Scheme.Hom.image_top_eq_opensRange,
          Scheme.Hom.opensRange_of_isIso])).op z =
      P.presheaf.map (eqToHom (show (f ≫ U.ι) ''ᵁ ⊤ = V by
        simp [V, Scheme.Hom.comp_image])).op (P.presheaf.map i.op z) := by
    change (P.presheaf.map _ ) z =
      ((P.presheaf.map i.op) ≫ (P.presheaf.map _)) z
    rw [← CategoryTheory.Functor.map_comp]
    congr 1
  exact (congrArg (fun z =>
    (schemeModuleHomCompositeRestriction M N U f h).app ⊤ z) (hmap M r)).trans
      (hall.trans (hmap N (schemeModuleHomSectionEvaluation M N U h r)).symm)
end LinearStudy
