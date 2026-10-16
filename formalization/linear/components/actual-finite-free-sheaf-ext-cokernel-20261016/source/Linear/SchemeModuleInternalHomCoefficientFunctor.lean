module
public import Linear.SchemeModuleHomPostcompose
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- ACTUAL internal Hom,covariant in the coefficient sheaf. This is the
functor whose right derived functors define derived internal SHEAF Ext;
no global projectivity of locally free sheaves is asserted. -/
def schemeModuleInternalHomCoefficientFunctor (X : Scheme.{u}) (P : X.Modules) :
    X.Modules ⥤ X.Modules where
  obj M := schemeModuleHomModuleSheaf P M
  map c := schemeModuleHomPostcompose c
  map_id M := schemeModuleHomPostcompose_id
  map_comp c d := schemeModuleHomPostcompose_comp c d

instance schemeModuleInternalHomCoefficientFunctor_additive (X : Scheme.{u}) (P : X.Modules) :
    (schemeModuleInternalHomCoefficientFunctor X P).Additive where
  map_add := fun {A B c d} => schemeModuleHomPostcompose_add c d

/-- The actual coefficient-functor map retains original local evaluation. -/
theorem schemeModuleInternalHomCoefficientFunctor_map_app {X : Scheme.{u}} (P : X.Modules)
    {M N : X.Modules} (c : M ⟶ N) (U : X.Opens)
    (f : Γ(schemeModuleHomModuleSheaf P M,U)) (W : (CategoryTheory.Over U)ᵒᵖ)
    (x : Γ(P,W.unop.left)) :
    (((schemeModuleInternalHomCoefficientFunctor X P).map c).app U f).val.app W x =
      c.app W.unop.left (f.val.app W x) :=
  schemeModuleHomPostcompose_app c U f W x

end LinearStudy
