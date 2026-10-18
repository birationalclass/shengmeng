module
public import Linear.SchemeModuleHomUnitCurry
public import Linear.SchemeModuleHomPrecompose
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}}

/-- Source precomposition uses the SAME actual unit currying. -/
theorem schemeModuleHomUnitAddEquiv_symm_precompose {P Q N : X.Modules}
    (g : P ⟶ Q) (f : Q ⟶ N) :
    (schemeModuleHomUnitAddEquiv P N).symm (g ≫ f) =
      (schemeModuleHomUnitAddEquiv Q N).symm f ≫
        schemeModuleHomPrecompose (N := N) g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro r
  apply Subtype.ext
  change (_ : (Over.forget U.unop).op ⋙ P.presheaf ⟶
    (Over.forget U.unop).op ⋙ N.presheaf) = _
  ext W x
  rfl

end LinearStudy
