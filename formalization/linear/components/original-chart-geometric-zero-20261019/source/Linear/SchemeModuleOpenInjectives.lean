module
public import Linear.OverOpenInjectiveRestriction
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory AlgebraicGeometry
universe u

/-- ACTUAL native module restriction for an ORIGINAL scheme,with its
constructed left adjoint;no local-injectivity hypothesis is supplied. -/
theorem schemeModuleOverFunctor_isRightAdjoint (X : Scheme.{u}) (U : X.Opens) :
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).IsRightAdjoint :=
  overOpenRestriction_isRightAdjoint X.ringCatSheaf U

/-- ACTUAL scheme-module restriction preserves injective objects. -/
theorem schemeModuleOverFunctor_preservesInjectiveObjects (X : Scheme.{u}) (U : X.Opens) :
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).PreservesInjectiveObjects :=
  overOpenRestriction_preservesInjectiveObjects X.ringCatSheaf U

/-- An actual injective module sheaf remains injective on EVERY original
open,derived from the CONSTRUCTED extension-by-zero adjunction. -/
theorem schemeModuleInjectiveOver (X : Scheme.{u}) (I : X.Modules) [Injective I] (U : X.Opens) :
    Injective (I.over U) := by
  letI := schemeModuleOverFunctor_preservesInjectiveObjects X U
  exact Functor.injective_obj (SheafOfModules.overFunctor.{u} X.ringCatSheaf U) I

end LinearStudy
