module
public import Linear.AffineTildeTensorPullback
public import Linear.TildeCoefficientQuotientPushforward
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- ACTUAL original coefficient quotient sheaf is CONSTRUCTED isomorphic
to ACTUAL pushforward of ORIGINAL geometric pullback on SAME ORIGINAL
closed cut Spec R/I->Spec R. Original N arbitrary;no pullback iso,
flatness/FP/free/invertibility/CM comparison certificate is assumed.
The original geometric unit/value compatibility is a separate obligation. -/
def tildeCoefficientQuotientGeometricPullbackPushforwardIso (R : CommRingCat.{u})
    (J : Ideal R) (N : ModuleCat.{u} R) :
    tilde (ModuleCat.of R (N ⧸ (J • (⊤ : Submodule R N)))) ≅
      (Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj
        ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj (tilde N)) :=
  tildeCoefficientQuotientPushforwardIso R J N ≪≫
    (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).mapIso
      (affineTildeTensorPullbackIso R (CommRingCat.of (R ⧸ J)) N).symm

end LinearStudy