module
public import Linear.CoextensionEvaluationAtOne
public import Mathlib.LinearAlgebra.Dual.BaseChange
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
variable {R S K : Type u} [CommRing R] [CommRing S] [CommRing K]
variable [Algebra R S] [Algebra R K] [Module.Free R S] [Module.Finite R S]
/-- ACTUAL base change of the ORIGINAL restricted coextension dual.
Finite/free hypotheses are EXPLICIT here;no global freeness of original
geometric S/R is asserted. Reuse mathlib's actual dual base-change iso. -/
def coextensionOriginalDualTensorEquiv :
    K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) ≃ₗ[K]
        Module.Dual K (K ⊗[R] S) :=
  (coextensionOriginalDualEquiv (R:=R) (S:=S)).baseChange R K _ _ ≪≫ₗ
    (TensorProduct.isBaseChange R S K).toDualBaseChange
/-- The ACTUAL comparison retains the ORIGINAL dual values on pure
fiber tensors;no transported scalar or desired trace law is an input. -/
theorem coextensionOriginalDualTensorEquiv_tmul_apply
    (a : K) (ell : (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) (s : S) :
    coextensionOriginalDualTensorEquiv (a ⊗ₜ[R] ell) ((1:K) ⊗ₜ[R] s)=
      a * algebraMap R K ((coextensionOriginalDualEquiv (R:=R) (S:=S) ell) s) := by
  simpa only [coextensionOriginalDualTensorEquiv,LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul,TensorProduct.mk_apply] using
      (TensorProduct.isBaseChange R S K).toDualBaseChange_tmul a
        (coextensionOriginalDualEquiv (R:=R) (S:=S) ell) s
/-- Evaluation on the ACTUAL tensor unit is the base change of the
ORIGINAL eval-at-one. This is an algebraic finite-free comparison only;
original geometric local freeness,Ext comparison and top-H calibration
remain separate obligations. -/
theorem coextensionOriginalDualTensorEquiv_original_evaluation
    (a : K) (ell : (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) :
    coextensionOriginalDualTensorEquiv (a ⊗ₜ[R] ell) ((1:K) ⊗ₜ[R] (1:S))=
      a * algebraMap R K (coextensionOriginalEvaluationAtOne (R:=R) (S:=S)
        (show (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) from ell)) := by
  exact coextensionOriginalDualTensorEquiv_tmul_apply a ell (1:S)
end LinearStudy
