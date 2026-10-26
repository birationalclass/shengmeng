module
public import Linear.SchemeModuleHomPostcomposeSection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} {P M N : X.Modules}

/-- Postcompose ACTUAL internal-Hom sections by the SAME coefficient map,
as an ACTUAL morphism of O-module sheaves on the original scheme. -/
def schemeModuleHomPostcompose (c : M ⟶ N) :
    schemeModuleHomModuleSheaf P M ⟶ schemeModuleHomModuleSheaf P N := ⟨{
  app U := ModuleCat.ofHom {
    toFun := schemeModuleHomPostcomposeSection P M N c U.unop
    map_add' f g := by
      apply Subtype.ext
      change (_ : (Over.forget U.unop).op ⋙ P.presheaf ⟶
        (Over.forget U.unop).op ⋙ N.presheaf) = _
      ext W x
      change c.app W.unop.left (_ + _) = _
      exact map_add (c.app W.unop.left).hom _ _
    map_smul' r f := by
      apply Subtype.ext
      change (_ : (Over.forget U.unop).op ⋙ P.presheaf ⟶
        (Over.forget U.unop).op ⋙ N.presheaf) = _
      ext W x
      change c.app W.unop.left (X.presheaf.map W.unop.hom.op r •
        (show Γ(M,W.unop.left) from f.val.app W x)) = _
      exact Scheme.Modules.Hom.app_smul c _ _ }
  naturality i := by
    ext f
    apply Subtype.ext
    change (_ : (Over.forget _).op ⋙ P.presheaf ⟶
      (Over.forget _).op ⋙ N.presheaf) = _
    ext W x
    rfl }⟩

/-- The coefficient map retains the SAME original local evaluation. -/
theorem schemeModuleHomPostcompose_app (c : M ⟶ N) (U : X.Opens)
    (f : Γ(schemeModuleHomModuleSheaf P M,U)) (W : (Over U)ᵒᵖ)
    (x : Γ(P,W.unop.left)) :
    ((schemeModuleHomPostcompose c).app U f).val.app W x =
      c.app W.unop.left (f.val.app W x) := rfl

theorem schemeModuleHomPostcompose_id :
    schemeModuleHomPostcompose (P := P) (𝟙 M) =
      𝟙 (schemeModuleHomModuleSheaf P M) := by
  apply SheafOfModules.hom_ext
  ext U f
  apply Subtype.ext
  change (_ : (Over.forget U.unop).op ⋙ P.presheaf ⟶
    (Over.forget U.unop).op ⋙ M.presheaf) = _
  ext W x
  rfl

theorem schemeModuleHomPostcompose_comp {T : X.Modules}
    (c : M ⟶ N) (d : N ⟶ T) :
    schemeModuleHomPostcompose (P := P) (c ≫ d) =
      schemeModuleHomPostcompose c ≫ schemeModuleHomPostcompose d := by
  apply SheafOfModules.hom_ext
  ext U f
  apply Subtype.ext
  change (_ : (Over.forget U.unop).op ⋙ P.presheaf ⟶
    (Over.forget U.unop).op ⋙ T.presheaf) = _
  ext W x
  rfl

theorem schemeModuleHomPostcompose_add (c d : M ⟶ N) :
    schemeModuleHomPostcompose (P := P) (c + d) =
      schemeModuleHomPostcompose c + schemeModuleHomPostcompose d := by
  apply SheafOfModules.hom_ext
  ext U f
  apply Subtype.ext
  change (_ : (Over.forget U.unop).op ⋙ P.presheaf ⟶
    (Over.forget U.unop).op ⋙ N.presheaf) = _
  ext W x
  rfl

end LinearStudy
