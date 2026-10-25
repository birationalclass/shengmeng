module
public import Linear.SchemeModuleInternalHomCoefficientFunctor
public import Linear.SchemeModuleInternalHomComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} {P' P : X.Modules}

/-- ACTUAL source precomposition is natural in the coefficient sheaf.
The square uses original local maps in both variables. -/
def schemeModuleInternalHomSourceNatTrans (u : P' ⟶ P) :
    schemeModuleInternalHomCoefficientFunctor X P ⟶
      schemeModuleInternalHomCoefficientFunctor X P' where
  app N := schemeModuleHomPrecompose u
  naturality {M N} c := by
    apply SheafOfModules.hom_ext
    ext U f
    apply Subtype.ext
    change (_ : (Over.forget U.unop).op ⋙ P'.presheaf ⟶
      (Over.forget U.unop).op ⋙ N.presheaf) = _
    ext W x
    rfl

theorem schemeModuleInternalHomSourceNatTrans_id (P : X.Modules) :
    schemeModuleInternalHomSourceNatTrans (𝟙 P) =
      𝟙 (schemeModuleInternalHomCoefficientFunctor X P) := by
  apply NatTrans.ext
  funext N
  exact schemeModuleHomPrecompose_id

theorem schemeModuleInternalHomSourceNatTrans_comp {P'' : X.Modules}
    (u : P'' ⟶ P') (v : P' ⟶ P) :
    schemeModuleInternalHomSourceNatTrans (u ≫ v) =
      schemeModuleInternalHomSourceNatTrans v ≫ schemeModuleInternalHomSourceNatTrans u := by
  apply NatTrans.ext
  funext N
  exact schemeModuleHomPrecompose_comp u v

/-- ACTUAL internal Hom as a bifunctor of original module sheaves. -/
def schemeModuleInternalHomBifunctor (X : Scheme.{u}) :
    X.Modulesᵒᵖ ⥤ (X.Modules ⥤ X.Modules) where
  obj P := schemeModuleInternalHomCoefficientFunctor X P.unop
  map u := schemeModuleInternalHomSourceNatTrans u.unop
  map_id P := schemeModuleInternalHomSourceNatTrans_id P.unop
  map_comp u v := schemeModuleInternalHomSourceNatTrans_comp v.unop u.unop

/-- Fixing the actual coefficient returns the SAME previously constructed
contravariant internal-Hom functor used by the original Koszul complex. -/
theorem schemeModuleInternalHomBifunctor_flip_obj (X : Scheme.{u}) (N : X.Modules) :
    (schemeModuleInternalHomBifunctor X).flip.obj N = schemeModuleInternalHomFunctor X N := rfl

end LinearStudy
