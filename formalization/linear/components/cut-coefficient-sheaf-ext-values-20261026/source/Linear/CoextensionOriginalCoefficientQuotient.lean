module
public import Linear.SurjectiveBaseCoefficientQuotient
public import Linear.CoextensionNativeTopDualityInputs
public import Linear.TildeCoefficientQuotientPushforward
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [Algebra R K]
variable [IsScalarTower K R S] [IsScalarTower K R K]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
/-- ACTUAL native coextension coefficient modulo the ACTUAL fiber ideal
is its SAME original coefficient residue tensor,over the ORIGINAL field.
No free/flat/finite input and no transported source module action. -/
def coextensionOriginalCoefficientQuotientFiberEquiv
    (hres : Function.Surjective (algebraMap R K)) :
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    let C := (ModuleCat.restrictScalars (algebraMap R S)).obj D
    letI : IsScalarTower K S D := IsScalarTower.of_compHom K S D
    (D ⧸ ((RingHom.ker (algebraMap R K)).map (algebraMap R S) •
      (⊤ : Submodule S D))) ≃ₗ[K] K ⊗[R] C := by
  dsimp only
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  letI : IsScalarTower R S D := IsScalarTower.of_compHom R S D
  letI : IsScalarTower K S D := IsScalarTower.of_compHom K S D
  letI : IsScalarTower K R D := coextensionOriginalBaseScalarTower
  let e := restrictedScalarTowerModuleEquiv (R:=R) (S:=S) D
  exact (surjectiveBaseCoefficientQuotientOriginalFieldEquiv (S:=S) (N:=D) hres).trans
    (e.symm.baseChange R K _ _)
/-- Every ORIGINAL coextension coefficient class is mapped to1 tensor
that same native coefficient,viewed by the ACTUAL scalar restriction. -/
theorem coextensionOriginalCoefficientQuotientFiberEquiv_mk
    (hres : Function.Surjective (algebraMap R K))
    (ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) :
    coextensionOriginalCoefficientQuotientFiberEquiv hres (Submodule.Quotient.mk ell)=
      ((1:K) ⊗ₜ[R] (show (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from ell)) := by
  simp only [coextensionOriginalCoefficientQuotientFiberEquiv,id_eq,LinearEquiv.trans_apply,
    surjectiveBaseCoefficientQuotientOriginalFieldEquiv_mk,LinearEquiv.baseChange_tmul]
  rfl
end LinearStudy
