module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 140000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {Y : Scheme.{u}} (S : TopCat.Sheaf RingCat Y) (α : Y.ringCatSheaf ⟶ S)
variable (M N : SheafOfModules.{u} S)

/-- Turn the SAME original base-module morphism into an actual source-module
sheaf morphism, using its proved local scalar relation. Underlying sections,
maps and naturality are retained; there is no replacement comparison. -/
def originalBaseMorphismSourceLift
    (C : (show Y.Modules from (SheafOfModules.restrictScalars α).obj M) ⟶
      (show Y.Modules from (SheafOfModules.restrictScalars α).obj N))
    (hlocal : ∀ (W : Y.Opens) (b : S.obj.obj (op W)) (x : M.val.obj (op W)),
      C.app W (b • x) = b • (show N.val.obj (op W) from C.app W x)) : M ⟶ N := by
  refine {val := (PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map C.val) ?_)}
  intro W b x
  exact hlocal W.unop b x

theorem originalBaseMorphismSourceLift_app
    (C : (show Y.Modules from (SheafOfModules.restrictScalars α).obj M) ⟶
      (show Y.Modules from (SheafOfModules.restrictScalars α).obj N))
    (hlocal : ∀ (W : Y.Opens) (b : S.obj.obj (op W)) (x : M.val.obj (op W)),
      C.app W (b • x) = b • (show N.val.obj (op W) from C.app W x))
    (W : Y.Opens) (x : M.val.obj (op W)) :
    (originalBaseMorphismSourceLift S α M N C hlocal).val.app (op W) x = C.app W x := rfl

theorem originalBaseMorphismSourceLift_scalar_recovery
    (C : (show Y.Modules from (SheafOfModules.restrictScalars α).obj M) ⟶
      (show Y.Modules from (SheafOfModules.restrictScalars α).obj N))
    (hlocal : ∀ (W : Y.Opens) (b : S.obj.obj (op W)) (x : M.val.obj (op W)),
      C.app W (b • x) = b • (show N.val.obj (op W) from C.app W x)) :
    (SheafOfModules.restrictScalars α).map
      (originalBaseMorphismSourceLift S α M N C hlocal) = C := by
  ext W x
  rfl
end LinearStudy
