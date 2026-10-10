module
public import Linear.AffineCompositeHEq
public import Linear.SchemeModuleScalarNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 300000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- Actual original scalar endomorphism, inferred without comparing unrelated category expressions. -/
def affineHomScalarEnd (U : X.Opens) (R : CommRingCat.{u}) (e : ↑U ≅ Spec R)
    (r : Γ(X,U)) :=
  originalGlobalModuleScalar (X := Spec R) (e.inv.appTop (U.topIso.inv r))
    (N.restrict (e.inv ≫ U.ι))

def affineHomScaledTransport (U : X.Opens) (R : CommRingCat.{u}) (e : ↑U ≅ Spec R)
    (r : Γ(X,U)) (h : Γ(schemeModuleHomModuleSheaf M N,U)) :=
  affineCompositeInstantiation M N U R e h ≫ affineHomScalarEnd N U R e r

/-- EXACT original affine comparison carries r h to the actual same scalar multiple.
HEq retains the identical actual morphism while avoiding a Lean category-alias elaboration loop. -/
theorem affineHomScalarHEq (U : X.Opens) (R : CommRingCat.{u}) (e : ↑U ≅ Spec R)
    (r : Γ(X,U)) (h : Γ(schemeModuleHomModuleSheaf M N,U)) :
    HEq (schemeModuleHomAffineChartSectionsEquiv M N U R e (r • h))
      (affineHomScaledTransport M N U R e r h) := by
  have hE := affineCompositeHEq M N U R e (r • h)
  have hT := schemeModuleHomCompositeRestriction_smul M N U e.inv r h
  exact hE.trans (heq_of_eq hT)

end LinearStudy
