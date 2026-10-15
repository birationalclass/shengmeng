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
variable {X : Scheme.{u}} {M' M N : X.Modules}

/-- Precompose a genuine local Hom section by the actual restriction of
an original module-sheaf morphism. This later supplies the source-algebra
action on the finite dual. -/
def schemeModuleHomPrecomposeSection (u : M' ⟶ M) (U : X.Opens)
    (f : Γ(schemeModuleHomModuleSheaf M N,U)) :
    Γ(schemeModuleHomModuleSheaf M' N,U) :=
  schemeModuleHomOverEquiv M' N U
    (((SheafOfModules.overFunctor X.ringCatSheaf U).map u) ≫
      (schemeModuleHomOverEquiv M N U).symm f)

/-- Actual O-linear internal Hom is contravariant in its source module.
This morphism is O-linear and commutes with every ORIGINAL restriction. -/
def schemeModuleHomPrecompose (u : M' ⟶ M) :
    schemeModuleHomModuleSheaf M N ⟶ schemeModuleHomModuleSheaf M' N := ⟨{
  app U := ModuleCat.ofHom {
    toFun := schemeModuleHomPrecomposeSection u U.unop
    map_add' f g := by
      apply Subtype.ext
      change (_ : (Over.forget U.unop).op ⋙ M'.presheaf ⟶
        (Over.forget U.unop).op ⋙ N.presheaf) = _
      ext W x
      rfl
    map_smul' r f := by
      apply Subtype.ext
      change (_ : (Over.forget U.unop).op ⋙ M'.presheaf ⟶
        (Over.forget U.unop).op ⋙ N.presheaf) = _
      ext W x
      rfl }
  naturality i := by
    ext f
    apply Subtype.ext
    change (_ : (Over.forget _).op ⋙ M'.presheaf ⟶
      (Over.forget _).op ⋙ N.presheaf) = _
    ext W x
    rfl }⟩

/-- Precomposition retains the exact original evaluation, rather than
merely constructing an unspecified equivalent functional. -/
theorem schemeModuleHomPrecompose_app (u : M' ⟶ M) (U : X.Opens)
    (f : Γ(schemeModuleHomModuleSheaf M N,U)) (W : (Over U)ᵒᵖ)
    (x : Γ(M',W.unop.left)) :
    ((schemeModuleHomPrecompose u).app U f).val.app W x =
      f.val.app W (u.app W.unop.left x) := rfl

theorem schemeModuleHomPrecompose_id :
    schemeModuleHomPrecompose (𝟙 M : M ⟶ M) =
      𝟙 (schemeModuleHomModuleSheaf M N) := by
  apply SheafOfModules.hom_ext
  ext U f
  apply Subtype.ext
  change (_ : (Over.forget U.unop).op ⋙ M.presheaf ⟶
    (Over.forget U.unop).op ⋙ N.presheaf) = _
  ext W x
  rfl

theorem schemeModuleHomPrecompose_comp {M'' : X.Modules}
    (u : M'' ⟶ M') (v : M' ⟶ M) :
    schemeModuleHomPrecompose (N := N) (u ≫ v) =
      schemeModuleHomPrecompose v ≫ schemeModuleHomPrecompose u := by
  apply SheafOfModules.hom_ext
  ext U f
  apply Subtype.ext
  change (_ : (Over.forget U.unop).op ⋙ M''.presheaf ⟶
    (Over.forget U.unop).op ⋙ N.presheaf) = _
  ext W x
  rfl

theorem schemeModuleHomPrecompose_add (u v : M' ⟶ M) :
    schemeModuleHomPrecompose (N := N) (u + v) =
      schemeModuleHomPrecompose u + schemeModuleHomPrecompose v := by
  apply SheafOfModules.hom_ext
  ext U f
  apply Subtype.ext
  change (_ : (Over.forget U.unop).op ⋙ M'.presheaf ⟶
    (Over.forget U.unop).op ⋙ N.presheaf) = _
  ext W x
  change f.val.app W ((show Γ(M,W.unop.left) from u.app W.unop.left x) +
    (show Γ(M,W.unop.left) from v.app W.unop.left x)) = _
  exact map_add (f.val.app W).hom _ _

end LinearStudy
