module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Equivalence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
/-- ACTUAL native module restriction along a scheme isomorphism,with the inverse
restriction and the actual native composition/identity isomorphisms. -/
def schemeModuleIsoRestrictionEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor e.inv) (Scheme.Modules.restrictFunctor e.hom)
    ((Scheme.Modules.restrictFunctorId (X := X)).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).symm ≪≫
      Scheme.Modules.restrictFunctorComp e.hom e.inv)
    ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫
      Scheme.Modules.restrictFunctorId (X := Y))
/-- This SAME original restriction functor is an equivalence,not an assumed certificate. -/
theorem schemeModuleIsoRestriction_isEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.restrictFunctor e.inv).IsEquivalence :=
  inferInstanceAs (schemeModuleIsoRestrictionEquivalence e).functor.IsEquivalence
end LinearStudy
