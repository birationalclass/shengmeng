module
public import Linear.SchemeModuleHomModuleSections
public import Linear.SchemeModuleIsoPushforwardRestriction
public import Mathlib.CategoryTheory.HomCongr
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- Actual internal Hom sections on the SAME open are actual morphisms
of the restricted modules, through mathlib's original Over equivalence. -/
def schemeModuleHomOpenSectionsEquiv (U : X.Opens) :
    Γ(schemeModuleHomModuleSheaf M N,U) ≃
      (M.restrict U.ι ⟶ N.restrict U.ι) :=
  (schemeModuleHomModuleSectionsEquiv M N U).trans
    ((Scheme.Modules.overEquiv U).fullyFaithfulFunctor.homEquiv.trans
      (Iso.homCongr ((Scheme.Modules.overFunctorEquiv U).app M)
        ((Scheme.Modules.overFunctorEquiv U).app N)))

/-- Actual global internal Hom sections on an ORIGINAL affine chart
are actual morphisms between those SAME modules restricted to Spec R.
This uses the given scheme chart isomorphism and proven full faithfulness
of actual pushforward along its inverse; no Hom comparison is assumed. -/
def schemeModuleHomAffineChartSectionsEquiv (U : X.Opens)
    (R : CommRingCat.{u}) (e : ↑U ≅ Spec R) :
    Γ(schemeModuleHomModuleSheaf M N,U) ≃
      (M.restrict (e.inv ≫ U.ι) ⟶ N.restrict (e.inv ≫ U.ι)) :=
  (schemeModuleHomOpenSectionsEquiv M N U).trans
    (((Functor.FullyFaithful.ofFullyFaithful (Scheme.Modules.pushforward e.hom)).ofIso
      (schemeModuleIsoPushforwardRestriction e)).homEquiv.trans
      (Iso.homCongr ((Scheme.Modules.restrictFunctorComp e.inv U.ι).symm.app M)
        ((Scheme.Modules.restrictFunctorComp e.inv U.ι).symm.app N)))

end LinearStudy
