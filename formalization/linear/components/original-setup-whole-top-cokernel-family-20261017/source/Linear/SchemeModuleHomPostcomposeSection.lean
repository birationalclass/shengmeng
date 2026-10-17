module
public import Linear.SchemeModuleHomEvaluationRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {Y : Scheme.{u}} (P M N : Y.Modules)

/-- Postcompose an actual local Hom section by the actual base-module
sheaf morphism, using the original Over restriction functor. -/
def schemeModuleHomPostcomposeSection (C : M ⟶ N) (U : Y.Opens)
    (h : Γ(schemeModuleHomModuleSheaf P M,U)) :
    Γ(schemeModuleHomModuleSheaf P N,U) :=
  (schemeModuleHomOverEquiv P N U)
    ((schemeModuleHomOverEquiv P M U).symm h ≫
      (SheafOfModules.overFunctor Y.ringCatSheaf U).map C)

theorem schemeModuleHomPostcomposeSection_evaluation (C : M ⟶ N) (U : Y.Opens)
    (h : Γ(schemeModuleHomModuleSheaf P M,U)) (b : Γ(P,U)) :
    schemeModuleHomSectionEvaluation P N U (schemeModuleHomPostcomposeSection P M N C U h) b =
      C.app U (schemeModuleHomSectionEvaluation P M U h b) := rfl
end LinearStudy
