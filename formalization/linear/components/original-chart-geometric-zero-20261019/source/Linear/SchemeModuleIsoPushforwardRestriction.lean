module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
variable {X Y : Scheme.{u}}

/-- For the SAME actual scheme isomorphism, direct image is restriction
along its inverse. This uses actual pushforward composition and the
existing restriction counit, not a chosen equivalence of modules. -/
def schemeModuleIsoPushforwardRestriction (e : X ≅ Y) :
    Scheme.Modules.pushforward e.hom ≅ Scheme.Modules.restrictFunctor e.inv :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorAdjCounitIso e.inv).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pushforwardComp e.hom e.inv) _ ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pushforwardCongr e.hom_inv_id) _ ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pushforwardId X) _ ≪≫
    Functor.leftUnitor _

end LinearStudy
