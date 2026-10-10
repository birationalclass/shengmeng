module
public import Linear.SchemeModuleHomSheaf
public import Linear.SchemeModuleHomRestriction
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

/-- Global sections of the constructed local O-linear Hom sheaf are
EXACTLY actual morphisms of the original sheaves of O-modules. -/
def schemeModuleHomGlobalEquiv :
    (schemeModuleHomPresheaf M N).sections ≃ (M ⟶ N) where
  toFun s := by
    let t : (presheafHom M.presheaf N.presheaf).sections :=
      ⟨fun U => (s.val U).val, fun i => congrArg Subtype.val (s.property i)⟩
    let f := presheafHomSectionsEquiv M.presheaf N.presheaf t
    exact ⟨{
      app U := ModuleCat.ofHom {
        toFun := f.app U
        map_add' := map_add (f.app U).hom
        map_smul' := (s.val U).property (op (Over.mk (𝟙 U.unop))) }
      naturality i := by
        ext x
        exact congr($(f.naturality i) x) }⟩
  invFun f := by
    let t := (presheafHomSectionsEquiv M.presheaf N.presheaf).symm f.mapPresheaf
    refine ⟨fun U => ⟨t.val U, ?_⟩, ?_⟩
    · intro W r x
      exact Scheme.Modules.Hom.app_smul f r x
    · intro U V i
      apply Subtype.ext
      exact t.property i
  left_inv s := by
    apply Subtype.ext
    funext U
    apply Subtype.ext
    let t : (presheafHom M.presheaf N.presheaf).sections :=
      ⟨fun U => (s.val U).val, fun i => congrArg Subtype.val (s.property i)⟩
    exact congrArg (fun z => z.val U)
      ((presheafHomSectionsEquiv M.presheaf N.presheaf).symm_apply_apply t)
  right_inv f := by
    apply SheafOfModules.hom_ext
    ext U x
    rfl

end LinearStudy
