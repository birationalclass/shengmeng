module
public import Linear.TildePushforward
public import Mathlib.CategoryTheory.Adjunction.Unique
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- ACTUAL global-section functor of ACTUAL affine pushforward is
NATURALLY identified with ACTUAL original scalar restriction of global
sections. Reuse pinned native pushforward/forgetful natural iso on ALL
original module sheaves;no QC/FP or desired naturality certificate. -/
def affinePushforwardGlobalSectionsNatIso {R S : CommRingCat.{u}} (phi : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map phi) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars phi.hom := by
  let F : TopCat.Sheaf (ModuleCat.{u} R) (Spec R) ⥤ ModuleCat.{u} R :=
    TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤)
  exact CategoryTheory.Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso phi) F

end LinearStudy