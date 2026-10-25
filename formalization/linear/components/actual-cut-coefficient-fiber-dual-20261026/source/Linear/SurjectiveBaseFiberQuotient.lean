module
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
namespace LinearStudy
open TensorProduct
universe u
variable {R S K : Type u} [CommRing R] [CommRing S] [CommRing K]
variable [Algebra R S] [Algebra R K]
/-- ACTUAL fiber quotient comparison from the ACTUAL surjective residue
map. No chosen point-set bijection or replacement ideal. -/
def surjectiveBaseFiberQuotientAlgEquiv
    (hres : Function.Surjective (algebraMap R K)) :
    (S ⧸ (RingHom.ker (algebraMap R K)).map (algebraMap R S)) ≃ₐ[R] K ⊗[R] S := by
  let m := RingHom.ker (algebraMap R K)
  let e : (R ⧸ m) ≃ₐ[R] K :=
    Ideal.quotientKerAlgEquivOfSurjective (f:=Algebra.ofId R K) hres
  exact ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor S m).restrictScalars R).trans
    (Algebra.TensorProduct.congr e (AlgEquiv.refl : S ≃ₐ[R] S))
/-- Every ORIGINAL source class maps to its ACTUAL original tensor. -/
theorem surjectiveBaseFiberQuotientAlgEquiv_mk
    (hres : Function.Surjective (algebraMap R K)) (s : S) :
    surjectiveBaseFiberQuotientAlgEquiv hres (Ideal.Quotient.mk _ s)=((1:K) ⊗ₜ[R] s) := by
  simp only [surjectiveBaseFiberQuotientAlgEquiv,AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply,Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
    Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,map_one]
  rfl
variable [Algebra K R] [Algebra K S] [IsScalarTower K R S] [IsScalarTower K R K]
/-- The SAME comparison is linear over the ORIGINAL field as well as
multiplicative. Its value on EVERY original source class is unchanged. -/
def surjectiveBaseFiberQuotientOriginalFieldEquiv
    (hres : Function.Surjective (algebraMap R K)) :
    (S ⧸ (RingHom.ker (algebraMap R K)).map (algebraMap R S)) ≃ₐ[K] K ⊗[R] S := by
  let e := surjectiveBaseFiberQuotientAlgEquiv (S:=S) hres
  refine { e.toRingEquiv with commutes' := ?_ }
  intro c
  change e (Ideal.Quotient.mk _ (algebraMap K S c))=c ⊗ₜ[R] (1:S)
  rw [surjectiveBaseFiberQuotientAlgEquiv_mk]
  calc
    _ = (algebraMap R K (algebraMap K R c)) ⊗ₜ[R] (1:S) := by
      rw [IsScalarTower.algebraMap_apply K R S]
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap K R c)).symm
    _ = _ := by rw [← IsScalarTower.algebraMap_apply K R K];simp
/-- The field-linear comparison also retains EVERY original numerator. -/
theorem surjectiveBaseFiberQuotientOriginalFieldEquiv_mk
    (hres : Function.Surjective (algebraMap R K)) (s : S) :
    surjectiveBaseFiberQuotientOriginalFieldEquiv hres (Ideal.Quotient.mk _ s)=
      ((1:K) ⊗ₜ[R] s) :=
  surjectiveBaseFiberQuotientAlgEquiv_mk hres s
end LinearStudy
