module
public import Linear.SchemeModuleHomPrecompose
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}} {P' P N : X.Modules}

/-- Precompose INTERNAL Hom on the actual original open U by an ACTUAL
local O-module morphism;no globally extending source map is required. -/
def schemeModuleLocalHomPrecompose (U : X.Opens) (u : P'.over U ⟶ P.over U) :
    (schemeModuleHomModuleSheaf P N).over U ⟶
      (schemeModuleHomModuleSheaf P' N).over U := ⟨{
  app W := ModuleCat.ofHom {
    toFun := fun f => schemeModuleHomOverEquiv P' N W.unop.left
      (schemeModuleHomRestrict P' P W.unop.hom u ≫
        (schemeModuleHomOverEquiv P N W.unop.left).symm f)
    map_add' f g := by
      apply Subtype.ext
      change (_ : (Over.forget W.unop.left).op ⋙ P'.presheaf ⟶
        (Over.forget W.unop.left).op ⋙ N.presheaf) = _
      ext T x
      rfl
    map_smul' r f := by
      apply Subtype.ext
      change (_ : (Over.forget W.unop.left).op ⋙ P'.presheaf ⟶
        (Over.forget W.unop.left).op ⋙ N.presheaf) = _
      ext T x
      rfl }
  naturality i := by
    ext f
    apply Subtype.ext
    change (_ : (Over.forget _).op ⋙ P'.presheaf ⟶
      (Over.forget _).op ⋙ N.presheaf) = _
    ext T x
    rfl }⟩

/-- Actual local precomposition preserves the identity source map. -/
theorem schemeModuleLocalHomPrecompose_id (P N : X.Modules) (U : X.Opens) :
    schemeModuleLocalHomPrecompose (N := N) U (𝟙 (P.over U)) =
      𝟙 ((schemeModuleHomModuleSheaf P N).over U) := by
  apply SheafOfModules.hom_ext
  ext W f
  apply Subtype.ext
  change (_ : (Over.forget W.unop.left).op ⋙ P.presheaf ⟶
    (Over.forget W.unop.left).op ⋙ N.presheaf) = _
  ext T x
  rfl

/-- The SAME actual local source composition is retained. -/
theorem schemeModuleLocalHomPrecompose_comp {P'' : X.Modules} (U : X.Opens)
    (u : P''.over U ⟶ P'.over U) (v : P'.over U ⟶ P.over U) :
    schemeModuleLocalHomPrecompose (N := N) U (u ≫ v) =
      schemeModuleLocalHomPrecompose U v ≫ schemeModuleLocalHomPrecompose U u := by
  apply SheafOfModules.hom_ext
  ext W f
  apply Subtype.ext
  change (_ : (Over.forget W.unop.left).op ⋙ P''.presheaf ⟶
    (Over.forget W.unop.left).op ⋙ N.presheaf) = _
  ext T x
  rfl

end LinearStudy
