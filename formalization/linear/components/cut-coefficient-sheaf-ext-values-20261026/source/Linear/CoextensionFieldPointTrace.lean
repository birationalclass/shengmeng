module
public import Linear.CoextensionEvaluationAtOne
public import Mathlib.LinearAlgebra.Dual.Lemmas
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
/-- For the ACTUAL coextension over the residue field,the ORIGINAL
evaluation-at-one is nonzero on multiplication by EVERY nonzero e.
No arbitrary perfect functional replaces this trace;A need not be a domain. -/
theorem coextensionFieldTrace_nonzero_element_exists_one
    (e : A) (he : e ≠ 0) :
    ∃ ell : (ModuleCat.coextendScalars (algebraMap K A)).obj (ModuleCat.of K K),
      coextensionOriginalEvaluationAtOne (R:=K) (S:=A) (e • ell)=1 := by
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one K he
  let ell : (ModuleCat.coextendScalars (algebraMap K A)).obj (ModuleCat.of K K) := (coextensionOriginalDualEquiv (R:=K) (S:=A)).symm f
  refine ⟨ell,?_⟩
  have hval := congrArg (fun g : Module.Dual K A => g e)
    ((coextensionOriginalDualEquiv (R:=K) (S:=A)).apply_symm_apply f)
  change ell e = f e at hval
  rw [coextensionOriginalEvaluationAtOne_apply,ModuleCat.CoextendScalars.smul_apply]
  simpa only [one_mul,hval] using hf
/-- The SAME actual trace takes1 on the ACTUAL idempotent-fixed
coefficient subspace. This is the algebraic fiber lemma only:the original
geometric coefficient/Ext base change is not supplied or asserted. -/
theorem coextensionFieldTrace_idempotent_fixed_exists_one
    (e : A) (he : e ≠ 0) (hi : e*e=e) :
    ∃ eta : (ModuleCat.coextendScalars (algebraMap K A)).obj (ModuleCat.of K K),
      e • eta=eta ∧ coextensionOriginalEvaluationAtOne (R:=K) (S:=A) eta=1 := by
  obtain ⟨ell,hell⟩ := coextensionFieldTrace_nonzero_element_exists_one (K:=K) e he
  refine ⟨e • ell,?_,hell⟩
  rw [← mul_smul,hi]
end LinearStudy
