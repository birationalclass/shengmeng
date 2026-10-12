module
public import Linear.OriginalSheafSourceRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 120000
namespace LinearStudy
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R S : Sheaf J RingCat.{w}} (H : SheafOfModules.{w} R)
variable [∀ U : Cᵒᵖ, Module (S.obj.obj U) (H.val.presheaf.obj U)]
variable (hres : ∀ ⦃U V : Cᵒᵖ⦄ (i : U ⟶ V) (b : S.obj.obj U) (x : H.val.presheaf.obj U),
      H.val.presheaf.map i (b • x) = S.obj.map i b • H.val.presheaf.map i x)
variable (α : R ⟶ S)
variable (hbase : ∀ (U : Cᵒᵖ) (r : R.obj.obj U) (x : H.val.presheaf.obj U),
      α.hom.app U r • x = r • x)

theorem originalSheafWithSourceAction_restrictIso_hom_apply
    (U : Cᵒᵖ) (x : H.val.presheaf.obj U) :
    (originalSheafWithSourceAction_restrictIso H hres α hbase).hom.val.app U x =
      (show H.val.obj U from x) := rfl

/-- The inverse scalar recovery is also the identity on the SAME
original section carrier, proved from the actual inverse law. -/
theorem originalSheafWithSourceAction_restrictIso_inv_apply
    (U : Cᵒᵖ) (x : H.val.obj U) :
    (originalSheafWithSourceAction_restrictIso H hres α hbase).inv.val.app U x =
      (show ((SheafOfModules.restrictScalars α).obj
        (originalSheafWithSourceAction H hres)).val.obj U from x) := by
  let e := originalSheafWithSourceAction_restrictIso H hres α hbase
  have h := congrArg (fun k : H ⟶ H => k.val.app U x) e.inv_hom_id
  change e.hom.val.app U (e.inv.val.app U x) = x at h
  rw [originalSheafWithSourceAction_restrictIso_hom_apply] at h
  exact h
end LinearStudy
