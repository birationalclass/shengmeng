module
public import Linear.SchemeModuleHomEvaluationRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 150000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {Y : Scheme.{u}} (S : TopCat.Sheaf RingCat Y)
variable (α : Y.ringCatSheaf ⟶ S) (M : SheafOfModules.{u} S)

/-- An actual module section x defines the actual local O-linear map
from the source ring, b |-> b*x. Its naturality and base linearity are
proved from the original source module, without an action certificate. -/
def sourceRingSectionHom (U : Y.Opens)
    (x : Γ((show Y.Modules from (SheafOfModules.restrictScalars α).obj M),U)) :
    let P : Y.Modules := (SheafOfModules.restrictScalars α).obj (SheafOfModules.unit S)
    let A : Y.Modules := (SheafOfModules.restrictScalars α).obj M
    Γ(schemeModuleHomModuleSheaf P A,U) := by
  let P : Y.Modules := (SheafOfModules.restrictScalars α).obj (SheafOfModules.unit S)
  let A : Y.Modules := (SheafOfModules.restrictScalars α).obj M
  letI (W : Y.Opensᵒᵖ) : Module (S.obj.obj W) (A.val.obj W) := (M.val.obj W).isModule
  let t : (presheafHom P.presheaf A.presheaf).obj (op U) := {
    app W := AddCommGrpCat.ofHom {
      toFun := fun b => (show S.obj.obj (op W.unop.left) from b) •
        (M.val.presheaf.map W.unop.hom.op (show M.val.presheaf.obj (op U) from x))
      map_zero' := by
        change (0 : S.obj.obj (op W.unop.left)) • M.val.presheaf.map W.unop.hom.op x = 0
        exact zero_smul _ _
      map_add' b c := by
        change ((show S.obj.obj (op W.unop.left) from b) +
          (show S.obj.obj (op W.unop.left) from c)) •
          M.val.presheaf.map W.unop.hom.op x =
          (show S.obj.obj (op W.unop.left) from b) •
            M.val.presheaf.map W.unop.hom.op x +
          (show S.obj.obj (op W.unop.left) from c) •
            M.val.presheaf.map W.unop.hom.op x
        exact add_smul _ _ _ }
    naturality W Z i := by
      ext b
      change S.obj.map i.unop.left.op (show S.obj.obj (op W.unop.left) from b) •
        M.val.presheaf.map Z.unop.hom.op x =
        M.val.presheaf.map i.unop.left.op
          ((show S.obj.obj (op W.unop.left) from b) • M.val.presheaf.map W.unop.hom.op x)
      have hm := M.val.map_smul i.unop.left.op (show S.obj.obj (op W.unop.left) from b) (M.val.presheaf.map W.unop.hom.op x)
      change M.val.presheaf.map i.unop.left.op
        ((show S.obj.obj (op W.unop.left) from b) • M.val.presheaf.map W.unop.hom.op x) =
        S.obj.map i.unop.left.op (show S.obj.obj (op W.unop.left) from b) • M.val.presheaf.map i.unop.left.op
          (M.val.presheaf.map W.unop.hom.op x) at hm
      rw [hm]
      congr 1
      have he : M.val.presheaf.map W.unop.hom.op ≫ M.val.presheaf.map i.unop.left.op =
          M.val.presheaf.map Z.unop.hom.op := by
        rw [← M.val.presheaf.map_comp,← op_comp,i.unop.w]
      exact (congr($(he) x)).symm }
  refine ⟨t,?_⟩
  intro W r b
  change (α.hom.app (op W.unop.left) r * (show S.obj.obj (op W.unop.left) from b)) •
    M.val.presheaf.map W.unop.hom.op x =
    α.hom.app (op W.unop.left) r •
      ((show S.obj.obj (op W.unop.left) from b) • M.val.presheaf.map W.unop.hom.op x)
  exact mul_smul _ _ _

theorem sourceRingSectionHom_evaluation (U : Y.Opens)
    (x : Γ((show Y.Modules from (SheafOfModules.restrictScalars α).obj M),U))
    (b : S.obj.obj (op U)) :
    let P : Y.Modules := (SheafOfModules.restrictScalars α).obj (SheafOfModules.unit S)
    let A : Y.Modules := (SheafOfModules.restrictScalars α).obj M
    schemeModuleHomSectionEvaluation P A U (sourceRingSectionHom S α M U x)
      (show Γ(P,U) from b) = b • (show M.val.obj (op U) from x) := by
  dsimp only
  change b • M.val.presheaf.map (𝟙 (op U)) x = b • (show M.val.obj (op U) from x)
  rw [M.val.presheaf.map_id]
  rfl
end LinearStudy
