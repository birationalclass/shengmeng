module
public import Linear.SchemeModuleHomAffineChartSections
public import Linear.SchemeModuleHomEvaluationRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- The actual open-scheme Hom comparison evaluates through the SAME
original section transport and actual restriction of the internal Hom. -/
theorem schemeModuleHomOpenSectionsEquiv_evaluation (U : X.Opens)
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) (W : (U : Scheme).Opens)
    (x : Γ(M,U.ι ''ᵁ W)) :
    let i : U.ι ''ᵁ W ⟶ U := homOfLE (by
      exact (Scheme.Hom.image_mono U.ι le_top).trans (le_of_eq U.ι_image_top))
    (schemeModuleHomOpenSectionsEquiv M N U h).app W
      ((M.restrictAppIso U.ι W).inv x) =
    (N.restrictAppIso U.ι W).inv
      (schemeModuleHomSectionEvaluation M N (U.ι ''ᵁ W)
        ((schemeModuleHomModuleSheaf M N).presheaf.map i.op h) x) := by
  dsimp only
  let i : U.ι ''ᵁ W ⟶ U := homOfLE (by
    exact (Scheme.Hom.image_mono U.ι le_top).trans (le_of_eq U.ι_image_top))
  change h.val.app (op (Over.mk i)) x =
    ((presheafHom M.presheaf N.presheaf).map i.op h.val).app
      (op (Over.mk (𝟙 (U.ι ''ᵁ W)))) x
  have H := presheafHom_map_app_op_mk_id (F := M.presheaf) (G := N.presheaf) i
    (show (presheafHom M.presheaf N.presheaf).obj (op U) from h.val)
  exact (congrArg (fun f : M.presheaf.obj (op (U.ι ''ᵁ W)) ⟶
      N.presheaf.obj (op (U.ι ''ᵁ W)) => f x) H).symm

end LinearStudy
