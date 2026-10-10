module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafHom
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

/-- The actual O-linear condition on a local morphism of the underlying
abelian sheaves. Scalars and sections belong to each original subopen. -/
def schemeModuleHomOverLinear (U : X.Opens)
    (f : (presheafHom M.presheaf N.presheaf).obj (op U)) : Prop :=
  ∀ (W : (Over U)ᵒᵖ) (r : Γ(X, W.unop.left)) (x : Γ(M, W.unop.left)),
    f.app W (r • x) = r • (show Γ(N, W.unop.left) from f.app W x)

/-- The genuine presheaf of local O-linear morphisms, obtained by restricting
mathlib's actual presheafHom. This is a presheaf construction; the sheaf
condition and O-module structure are separate obligations. -/
def schemeModuleHomPresheaf : X.Opensᵒᵖ ⥤ Type u where
  obj U := { f : (presheafHom M.presheaf N.presheaf).obj U //
    schemeModuleHomOverLinear M N U.unop f }
  map i := ↾fun f => ⟨(presheafHom M.presheaf N.presheaf).map i f.val,
    fun W r x => f.property ((Over.map i.unop).op.obj W) r x⟩
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact congr($((presheafHom M.presheaf N.presheaf).map_id U) f.val)
  map_comp i j := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact congr($((presheafHom M.presheaf N.presheaf).map_comp i j) f.val)

/-- Local O-linear morphisms in the constructed presheaf are exactly
ACTUAL morphisms of the original sheaves of modules on Over U. -/
def schemeModuleHomOverEquiv (U : X.Opens) :
    (M.over U ⟶ N.over U) ≃ (schemeModuleHomPresheaf M N).obj (op U) where
  toFun f := ⟨{
    app W := (forget₂ _ _).map (f.val.app W)
    naturality _ _ i := by
      ext x
      exact PresheafOfModules.naturality_apply f.val i x },
    fun W r x => (f.val.app W).hom.map_smul r x⟩
  invFun f := ⟨{
    app W := ModuleCat.ofHom {
      toFun := f.val.app W
      map_add' := map_add (f.val.app W).hom
      map_smul' := f.property W }
    naturality i := by
      ext x
      exact congr($(f.val.naturality i) x) }⟩
  left_inv f := by
    apply SheafOfModules.hom_ext
    ext W x
    rfl
  right_inv f := by
    apply Subtype.ext
    change (_ : (Over.forget U).op ⋙ M.presheaf ⟶ (Over.forget U).op ⋙ N.presheaf) = _
    ext W x
    rfl

end LinearStudy
