module
public import Linear.AffinePushforwardGlobalSectionsNaturality
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- ACTUAL geometric pullback of ORIGINAL affine tilde modules is
NATURALLY isomorphic to ACTUAL extension of scalars followed by tilde.
Both original functors are identified as left adjoints of the SAME
proved actual original pushforward/global-section functor. No comparison
iso,QC/FP/flatness or pullback compatibility is an input. -/
def affineTildePullbackExtendScalarsNatIso {R S : CommRingCat.{u}} (phi : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map phi) ≅
      ModuleCat.extendScalars phi.hom ⋙ tilde.functor S :=
  (((tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map phi))).ofNatIsoRight
      (affinePushforwardGlobalSectionsNatIso phi)).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj phi.hom).comp (tilde.adjunction (R := S)))

end LinearStudy