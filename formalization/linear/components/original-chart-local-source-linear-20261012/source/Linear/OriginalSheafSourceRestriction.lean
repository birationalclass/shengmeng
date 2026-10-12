module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R S : Sheaf J RingCat.{w}} (H : SheafOfModules.{w} R)
variable [∀ U : Cᵒᵖ, Module (S.obj.obj U) (H.val.presheaf.obj U)]

/-- Equip the SAME original sheaf with a proved action of a second sheaf
of rings. The underlying abelian presheaf and its sheaf proof are retained. -/
def originalSheafWithSourceAction
    (hres : ∀ ⦃U V : Cᵒᵖ⦄ (i : U ⟶ V) (b : S.obj.obj U) (x : H.val.presheaf.obj U),
      H.val.presheaf.map i (b • x) = S.obj.map i b • H.val.presheaf.map i x) :
    SheafOfModules S :=
  { val := PresheafOfModules.ofPresheaf (R := S.obj) H.val.presheaf hres,
    isSheaf := H.isSheaf }

/-- If the source action restricts to the original base action, restricting
scalars recovers the ORIGINAL sheaf, by the identity on sections. -/
def originalSheafWithSourceAction_restrictIso
    (hres : ∀ ⦃U V : Cᵒᵖ⦄ (i : U ⟶ V) (b : S.obj.obj U) (x : H.val.presheaf.obj U),
      H.val.presheaf.map i (b • x) = S.obj.map i b • H.val.presheaf.map i x)
    (α : R ⟶ S)
    (hbase : ∀ (U : Cᵒᵖ) (r : R.obj.obj U) (x : H.val.presheaf.obj U),
      α.hom.app U r • x = r • x) :
    (SheafOfModules.restrictScalars α).obj
      (originalSheafWithSourceAction H hres) ≅ H := by
  let M := (SheafOfModules.restrictScalars α).obj
    (originalSheafWithSourceAction H hres)
  let e (U : Cᵒᵖ) : M.val.obj U ≅ H.val.obj U := by
    let f : M.val.obj U →ₗ[R.obj.obj U] H.val.obj U :=
      { toFun := fun x ↦ x,
        map_add' := fun _ _ ↦ rfl,
        map_smul' := fun r x ↦ hbase U r x }
    exact (LinearEquiv.ofBijective f
      ⟨fun _ _ h ↦ h, fun x ↦ ⟨x, rfl⟩⟩).toModuleIso
  exact (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk e (by
      intro U V i
      apply ModuleCat.hom_ext
      ext x
      rfl))

end LinearStudy
