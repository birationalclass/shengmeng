module
public import Linear.SchemeModuleHomOpenEvaluation
public import Linear.SchemeModuleHomCompositeRestriction
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
variable {X Y : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
variable (f : Y ⟶ (U : Scheme)) [IsOpenImmersion f]

/-- Composite restriction evaluates using the original Hom section and
the actual composition isomorphisms, on every open of the chart. -/
theorem schemeModuleHomCompositeRestriction_evaluation
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) (W : Y.Opens)
    (x : Γ(M,U.ι ''ᵁ (f ''ᵁ W))) :
    let i : U.ι ''ᵁ (f ''ᵁ W) ⟶ U := homOfLE
      ((Scheme.Hom.image_mono U.ι le_top).trans (le_of_eq U.ι_image_top))
    let A := (Scheme.Modules.restrictFunctorComp f U.ι).symm.app M
    let B := (Scheme.Modules.restrictFunctorComp f U.ι).symm.app N
    (schemeModuleHomCompositeRestriction M N U f h).app W
      (A.hom.app W (((M.restrict U.ι).restrictAppIso f W).inv
        ((M.restrictAppIso U.ι (f ''ᵁ W)).inv x))) =
    B.hom.app W (((N.restrict U.ι).restrictAppIso f W).inv
      ((N.restrictAppIso U.ι (f ''ᵁ W)).inv
        (schemeModuleHomSectionEvaluation M N (U.ι ''ᵁ (f ''ᵁ W))
          ((schemeModuleHomModuleSheaf M N).presheaf.map i.op h) x))) := by
  dsimp only
  have H := ((Scheme.Modules.restrictFunctorComp f U.ι).symm.app M).hom_inv_id
  have hx := congrArg (fun k => k.app W
    (((M.restrict U.ι).restrictAppIso f W).inv
      ((M.restrictAppIso U.ι (f ''ᵁ W)).inv x))) H
  dsimp [schemeModuleHomCompositeRestriction] at hx ⊢
  rw [hx]
  exact congrArg
    (fun y => ((Scheme.Modules.restrictFunctorComp f U.ι).symm.app N).hom.app W y)
    (schemeModuleHomOpenSectionsEquiv_evaluation M N U h (f ''ᵁ W) x)

end LinearStudy
