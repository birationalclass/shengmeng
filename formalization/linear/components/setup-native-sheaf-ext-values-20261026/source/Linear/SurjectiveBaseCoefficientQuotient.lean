module
public import Linear.SurjectiveBaseFiberQuotient
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open TensorProduct
universe u
variable {R S K N : Type u} [CommRing R] [CommRing S] [CommRing K]
variable [Algebra R S] [Algebra R K] [AddCommGroup N]
variable [Module S N] [Module R N] [IsScalarTower R S N]
/-- Actual ORIGINAL coefficient quotient by the extended fiber ideal is
its actual residue tensor. No flatness,finiteness or arbitrary iso input.
This construction will be applied to the actual coextension coefficient. -/
def surjectiveBaseCoefficientQuotientEquiv
    (hres : Function.Surjective (algebraMap R K)) :
    (N ⧸ ((RingHom.ker (algebraMap R K)).map (algebraMap R S) •
      (⊤ : Submodule S N))) ≃ₗ[R] K ⊗[R] N := by
  let m := RingHom.ker (algebraMap R K)
  let P := m.map (algebraMap R S) • (⊤ : Submodule S N)
  have hP : P.restrictScalars R=m • (⊤ : Submodule R N) := by
    simpa only [P,Submodule.restrictScalars_top] using
      (Submodule.restrictScalars_map_smul_eq m (⊤ : Submodule S N))
  let e : (R ⧸ m) ≃ₐ[R] K :=
    Ideal.quotientKerAlgEquivOfSurjective (f:=Algebra.ofId R K) hres
  exact (Submodule.Quotient.restrictScalarsEquiv R P).symm.trans
    ((Submodule.quotEquivOfEq _ _ hP).trans
      ((TensorProduct.quotTensorEquivQuotSMul N m).symm.trans
        (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R N))))
/-- The actual quotient comparison retains EVERY original coefficient. -/
theorem surjectiveBaseCoefficientQuotientEquiv_mk
    (hres : Function.Surjective (algebraMap R K)) (n : N) :
    surjectiveBaseCoefficientQuotientEquiv (S:=S) hres (Submodule.Quotient.mk n)=
      ((1:K) ⊗ₜ[R] n) := by
  simp only [surjectiveBaseCoefficientQuotientEquiv,LinearEquiv.trans_apply,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk,Submodule.quotEquivOfEq_mk,
    TensorProduct.quotTensorEquivQuotSMul_symm_mk,TensorProduct.congr_tmul]
  change ((Ideal.quotientKerAlgEquivOfSurjective (f:=Algebra.ofId R K) hres)
    (1 : R ⧸ RingHom.ker (algebraMap R K))) ⊗ₜ[R] n=_
  simp only [map_one]
variable [Algebra K R] [Algebra K S] [IsScalarTower K R S] [IsScalarTower K R K]
variable [Module K N] [IsScalarTower K R N] [IsScalarTower K S N]
/-- The SAME original coefficient quotient comparison is linear over the
ORIGINAL coefficient field. This does not transport a source action. -/
def surjectiveBaseCoefficientQuotientOriginalFieldEquiv
    (hres : Function.Surjective (algebraMap R K)) :
    (N ⧸ ((RingHom.ker (algebraMap R K)).map (algebraMap R S) •
      (⊤ : Submodule S N))) ≃ₗ[K] K ⊗[R] N :=
  (surjectiveBaseCoefficientQuotientEquiv (S:=S) hres).restrictScalars K
/-- Original-field linearity leaves every original coefficient class unchanged. -/
theorem surjectiveBaseCoefficientQuotientOriginalFieldEquiv_mk
    (hres : Function.Surjective (algebraMap R K)) (n : N) :
    surjectiveBaseCoefficientQuotientOriginalFieldEquiv (S:=S) hres
      (Submodule.Quotient.mk n)=((1:K) ⊗ₜ[R] n) :=
  surjectiveBaseCoefficientQuotientEquiv_mk (R:=R) (S:=S) (K:=K) (N:=N) hres n
end LinearStudy
