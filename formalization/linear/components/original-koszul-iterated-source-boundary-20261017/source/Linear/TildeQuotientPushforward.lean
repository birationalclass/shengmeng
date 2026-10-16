module
public import Linear.TildePushforward
public import Linear.ExtendScalarsActualTensor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- The associated quotient module is the structure sheaf of the actual
closed subscheme pushed forward along the original quotient ring map. -/
def tildeQuotientPushforwardIso (R : CommRingCat.{u}) (J : Ideal R) :
    tilde (ModuleCat.of R (R ⧸ J)) ≅
      (Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj
        (SheafOfModules.unit.{u} (Spec (CommRingCat.of (R ⧸ J))).ringCatSheaf) := by
  let φ : R ⟶ CommRingCat.of (R ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let e : ((ModuleCat.restrictScalars φ.hom).obj
      (ModuleCat.of (R ⧸ J) (R ⧸ J))) ≅ ModuleCat.of R (R ⧸ J) :=
    (restrictedAlgebraModuleEquiv (R := R) (S := R ⧸ J)).toModuleIso
  exact (tilde.functor R).mapIso e.symm ≪≫
    tildePushforwardIso φ (ModuleCat.of (R ⧸ J) (R ⧸ J)) ≪≫
      (Scheme.Modules.pushforward (Spec.map φ)).mapIso tildeSelf

end LinearStudy
