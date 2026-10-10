module
public import Linear.SchemeModuleHomAffineChartSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}}
/-- The SAME original affine restriction composition isomorphism, with
its exact module endpoints retained for later Hom transport. -/
def schemeModuleAffineRestrictionIso (M : X.Modules)
    (U : X.Opens) (R : CommRingCat.{u}) (e : ↑U ≅ Spec R) :
    (M.restrict U.ι).restrict e.inv ≅ M.restrict (e.inv ≫ U.ι) :=
  Iso.app ((Scheme.Modules.restrictFunctorComp e.inv U.ι).symm) M
end LinearStudy
