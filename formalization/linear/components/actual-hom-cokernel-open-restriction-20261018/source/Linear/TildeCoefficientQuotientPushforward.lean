module
public import Linear.TildePushforward
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TensorProduct
universe u

/-- Identity on ORIGINAL elements compares categorical scalar restriction
with the SAME original tower module action. Used at the actual quotient
base-change tensor,whose scalar tower is canonical,not an input. -/
def restrictedScalarTowerModuleEquiv {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} S) [Module R M] [IsScalarTower R S M] :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj M) ≃ₗ[R] M where
  toFun x := x
  invFun x := x
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' r x := by
    simp only [ModuleCat.restrictScalars.smul_def]
    exact IsScalarTower.algebraMap_smul S r (show M from x)

/-- ACTUAL associated coefficient quotient N/I N is the ACTUAL pushforward
from SAME ORIGINAL cut Spec R/I of SAME ORIGINAL base-changed coefficient
(R/I) tensor_R N. Reuse actual tensor quotient equivalence and actual
native tildePushforwardIso. NO freeness/flatness/FP/CM of N or iso input. -/
def tildeCoefficientQuotientPushforwardIso (R : CommRingCat.{u}) (J : Ideal R)
    (N : ModuleCat.{u} R) :
    tilde (ModuleCat.of R (N ⧸ (J • (⊤ : Submodule R N)))) ≅
      (Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj
        (tilde (ModuleCat.of (R ⧸ J) ((R ⧸ J) ⊗[R] N))) := by
  let phi : R ⟶ CommRingCat.of (R ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let T := ModuleCat.of (R ⧸ J) ((R ⧸ J) ⊗[R] N)
  let e : (ModuleCat.restrictScalars phi.hom).obj T ≅
      ModuleCat.of R (N ⧸ (J • (⊤ : Submodule R N))) :=
    ((restrictedScalarTowerModuleEquiv (R := R) (S := R ⧸ J) T).trans
      (TensorProduct.quotTensorEquivQuotSMul N J)).toModuleIso
  exact (tilde.functor R).mapIso e.symm ≪≫ tildePushforwardIso phi T

end LinearStudy