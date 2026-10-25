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
variable [Algebra R S] [Algebra R K]
/-- Literal base change of ORIGINAL evaluation-at-one. This functional
exists without finite/free/flat/local-regularity assumptions and is NOT
defined using any comparison isomorphism or a chosen perfect functional. -/
def coextensionOriginalBaseChangedEvaluationAtOne :
    Module.Dual K (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) :=
  Module.Dual.baseChange K ((Module.Dual.eval R S (1:S)).comp
    (coextensionOriginalDualEquiv (R:=R) (S:=S)).toLinearMap)
/-- Exact ORIGINAL eval-at-one value on original pure coefficients. -/
theorem coextensionOriginalBaseChangedEvaluationAtOne_tmul
    (a : K) (ell : (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) :
    coextensionOriginalBaseChangedEvaluationAtOne (a ⊗ₜ[R] ell)=
      a * algebraMap R K (coextensionOriginalEvaluationAtOne (R:=R) (S:=S)
        (show (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) from ell)) := by
  rw [coextensionOriginalBaseChangedEvaluationAtOne,Module.Dual.baseChange_apply_tmul]
  rw [Algebra.smul_def]
  change algebraMap R K ((coextensionOriginalDualEquiv (R:=R) (S:=S) ell) (1:S))*a=
    a*algebraMap R K ((coextensionOriginalDualEquiv (R:=R) (S:=S) ell) (1:S))
  exact mul_comm _ _
end LinearStudy
