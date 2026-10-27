module
public import Linear.SchemeModuleIsoRestrictionEquivalence
public import Linear.SchemeModuleGlobalExtActualHCohomology
public import Linear.PointedExactFunctorExtZeroFullyFaithful
public import Linear.SchemeModuleOpenRestrictionExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
/-- Actual GLOBAL structure-unit Ext in every degree transports under an ACTUAL
scheme isomorphism using native restriction and its native unit isomorphism. -/
def schemeModuleSchemeIsoGlobalExtAddEquiv {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : X.Modules) (n : ℕ) :
    Ext.{u} (SheafOfModules.unit X.ringCatSheaf) M n ≃+
      Ext.{u} (SheafOfModules.unit Y.ringCatSheaf) (M.restrict e.inv) n := by
  let R := Scheme.Modules.restrictFunctor e.inv
  letI : R.IsEquivalence := schemeModuleIsoRestriction_isEquivalence e
  letI : R.Additive := schemeModuleOpenRestriction_additive e.inv
  letI : PreservesFiniteLimits R := schemeModuleOpenRestriction_preservesFiniteLimits e.inv
  let point := (Scheme.Modules.restrictUnitIso e.inv).inv
  exact AddEquiv.ofBijective (pointedExactFunctorExtMap R point M n)
    (pointedExactFunctorExtMap_bijective R point
      (fun N => pointedExactFunctorExtMap_zero_bijective_of_fullyFaithful R point N)
      (fun I _ j => by
        letI : Injective (R.obj I) := Functor.injective_obj R I
        exact subsingleton_of_forall_eq 0 (fun x => Ext.eq_zero_of_injective x)) M n)
end LinearStudy
