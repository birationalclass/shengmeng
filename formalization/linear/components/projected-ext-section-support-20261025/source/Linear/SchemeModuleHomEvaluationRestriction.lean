module
public import Linear.SchemeModuleHomModuleSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- Evaluation of an actual internal Hom section on the same original open. -/
def schemeModuleHomSectionEvaluation (U : X.Opens)
    (f : Γ(schemeModuleHomModuleSheaf M N,U)) :
    Γ(M,U) →ₗ[Γ(X,U)] Γ(N,U) where
  toFun := f.val.app (op (Over.mk (𝟙 U)))
  map_add' := map_add (f.val.app (op (Over.mk (𝟙 U)))).hom
  map_smul' := f.property (op (Over.mk (𝟙 U)))

/-- Evaluation commutes with the genuine restrictions of both original
module sheaves. No compatibility certificate is supplied. -/
theorem schemeModuleHomSectionEvaluation_restrict {U V : X.Opens} (i : V ⟶ U)
    (f : Γ(schemeModuleHomModuleSheaf M N,U)) (x : Γ(M,U)) :
    schemeModuleHomSectionEvaluation M N V
      ((schemeModuleHomModuleSheaf M N).presheaf.map i.op f)
      (M.presheaf.map i.op x) =
    N.presheaf.map i.op (schemeModuleHomSectionEvaluation M N U f x) := by
  change ((presheafHom M.presheaf N.presheaf).map i.op f.val).app
      (op (Over.mk (𝟙 V))) (M.presheaf.map i.op x) =
    N.presheaf.map i.op (f.val.app (op (Over.mk (𝟙 U))) x)
  have H := presheafHom_map_app_op_mk_id (F := M.presheaf) (G := N.presheaf) i
    (show (presheafHom M.presheaf N.presheaf).obj (op U) from f.val)
  exact (congrArg (fun h : M.presheaf.obj (op V) ⟶ N.presheaf.obj (op V) =>
      h (M.presheaf.map i.op x)) H).trans
    (congr($(f.val.naturality
      (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 U)).op) x))

end LinearStudy
