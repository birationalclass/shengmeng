module
public import Linear.AffineQuasicoherentSourceMorphisms
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 120000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {Y : Scheme.{u}} (S : TopCat.Sheaf RingCat Y)
variable (α : Y.ringCatSheaf ⟶ S) (M : SheafOfModules.{u} S)
variable [∀ W : Y.Opensᵒᵖ, SMulCommClass (S.obj.obj W) (S.obj.obj W) (M.val.obj W)]

/-- Multiplication by an actual global source-ring section is an
endomorphism of the SAME restricted base-module sheaf. All restrictions
and base linearity are proved from the actual source-module structure. -/
def sourceGlobalSectionMultiplication
    (b : S.obj.obj (op (⊤ : Y.Opens))) :
    let B : Y.Modules := (SheafOfModules.restrictScalars α).obj M
    B ⟶ B := by
  let B : Y.Modules := (SheafOfModules.restrictScalars α).obj M
  letI (W : Y.Opensᵒᵖ) : Module (S.obj.obj W) (B.val.obj W) :=
    (M.val.obj W).isModule
  letI (W : Y.Opensᵒᵖ) : SMulCommClass (S.obj.obj W) (S.obj.obj W) (B.val.obj W) :=
    inferInstanceAs (SMulCommClass (S.obj.obj W) (S.obj.obj W) (M.val.obj W))
  refine {val := {app := fun W => ModuleCat.ofHom (X := B.val.obj W) (Y := B.val.obj W) {
    toFun := fun x => S.obj.map W.unop.leTop.op b • (show M.val.obj W from x)
    map_add' := fun x y => smul_add _ x y
    map_smul' := fun r x => ?_ }, naturality := ?_}}
  · change S.obj.map W.unop.leTop.op b • (α.hom.app W r • x) =
      α.hom.app W r • (S.obj.map W.unop.leTop.op b • x)
    exact smul_comm _ _ _
  · intro U V i
    apply ModuleCat.hom_ext
    ext x
    change S.obj.map V.unop.leTop.op b • M.val.map i x =
      M.val.map i (S.obj.map U.unop.leTop.op b • x)
    symm
    rw [M.val.map_smul]
    congr 1
    have he : S.obj.map U.unop.leTop.op ≫ S.obj.map i = S.obj.map V.unop.leTop.op := by
      rw [← S.obj.map_comp]
      rfl
    exact congr($(he) b)

theorem sourceGlobalSectionMultiplication_app
    (b : S.obj.obj (op (⊤ : Y.Opens))) (W : Y.Opens)
    (x : Γ((show Y.Modules from (SheafOfModules.restrictScalars α).obj M),W)) :
    (sourceGlobalSectionMultiplication S α M b).app W x =
      S.obj.map W.leTop.op b • (show M.val.obj (op W) from x) := rfl
end LinearStudy
