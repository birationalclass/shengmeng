module
public import Linear.CoextensionFieldPointTrace
public import Linear.CoextensionOriginalDualTensorBaseChange
public import Mathlib.RingTheory.TensorProduct.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
variable {R S K : Type u} [CommRing R] [CommRing S] [Field K]
variable [Algebra R S] [Algebra R K] [Module.Free R S] [Module.Finite R S]
/-- The ORIGINAL S multiplication on actual coextension,restricted to
an R-linear map. No scalar action is transported through a dual comparison. -/
def coextensionOriginalScalarRLinear (s : S) : ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) →ₗ[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) where
  toFun ell := show ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) from s • (show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from ell)
  map_add' x y := by
    change s • ((show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from x)+(show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from y))=
      s • (show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from x)+s • (show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from y)
    exact smul_add _ _ _
  map_smul' r ell := by
    change s • (algebraMap R S r • (show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from ell))=
      algebraMap R S r • (s • (show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from ell))
    exact smul_comm _ _ _
/-- Base change of that SAME actual scalar endomorphism. -/
def coextensionOriginalScalarFiberEnd (s : S) : (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) →ₗ[K] (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) :=
  (coextensionOriginalScalarRLinear (R:=R) s).baseChange K
/-- ORIGINAL base-changed eval-at-one,defined at the ACTUAL tensor unit. -/
def coextensionOriginalFiberTrace : Module.Dual K (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) :=
  (Module.Dual.eval K (K ⊗[R] S) (1:(K ⊗[R] S))).comp
    (coextensionOriginalDualTensorEquiv (R:=R) (S:=S) (K:=K)).toLinearMap
attribute [local irreducible] coextensionOriginalDualTensorEquiv
/-- Values on BOTH actual pure tensors,from mathlib base change. -/
theorem coextensionOriginalDualTensorEquiv_both_tmul
    (a b : K) (ell : ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) (t : S) :
    coextensionOriginalDualTensorEquiv (a ⊗ₜ[R] ell) (b ⊗ₜ[R] t)=
      b * (a * algebraMap R K ((coextensionOriginalDualEquiv (R:=R) (S:=S) ell) t)) := by
  calc
    _ = coextensionOriginalDualTensorEquiv (a ⊗ₜ[R] ell)
        (b • ((1:K) ⊗ₜ[R] t)) := by
      rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    _ = b * coextensionOriginalDualTensorEquiv (a ⊗ₜ[R] ell) ((1:K) ⊗ₜ[R] t) := by
      rw [map_smul,smul_eq_mul]
    _ = _ := by rw [coextensionOriginalDualTensorEquiv_tmul_apply]
/-- The actual tensor comparison respects ORIGINAL S coefficient action.
It is a theorem about the original endomorphism,not a transported action. -/
theorem coextensionOriginalDualTensorEquiv_scalar_naturality
    (s : S) (m : (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))))) (z : (K ⊗[R] S)) :
    coextensionOriginalDualTensorEquiv
        (coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s m) z=
      coextensionOriginalDualTensorEquiv m (z*((1:K) ⊗ₜ[R] s)) := by
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => simp only [map_add,LinearMap.add_apply,hm,hn]
  | tmul a ell =>
    change coextensionOriginalDualTensorEquiv
      (a ⊗ₜ[R] (show ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) from s • (show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from ell))) z=
        coextensionOriginalDualTensorEquiv (a ⊗ₜ[R] ell) (z*((1:K) ⊗ₜ[R] s))
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [add_mul,map_add,hz,hw]
    | tmul b t =>
      rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one]
      rw [coextensionOriginalDualTensorEquiv_both_tmul,
        coextensionOriginalDualTensorEquiv_both_tmul]
      change b * (a * algebraMap R K ((s • (show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from ell)) t))=
        b * (a * algebraMap R K ((show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from ell) (t*s)))
      rw [ModuleCat.CoextendScalars.smul_apply]
/-- The actual ORIGINAL scalar tensor endomorphism is idempotent as soon
as its ACTUAL fiber scalar is idempotent. No transported coefficient action. -/
theorem coextensionOriginalScalarFiberEnd_idempotent (s : S)
    (hi : ((1:K) ⊗ₜ[R] s : K ⊗[R] S)*((1:K) ⊗ₜ[R] s)=((1:K) ⊗ₜ[R] s)) :
    ∀ m,coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s
      (coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s m)=
        coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s m := by
  intro m
  apply (coextensionOriginalDualTensorEquiv (R:=R) (S:=S) (K:=K)).injective
  apply LinearMap.ext
  intro z
  calc
    _ = coextensionOriginalDualTensorEquiv
        (coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s m) (z*((1:K) ⊗ₜ[R] s)) :=
      coextensionOriginalDualTensorEquiv_scalar_naturality s _ z
    _ = coextensionOriginalDualTensorEquiv m ((z*((1:K) ⊗ₜ[R] s))*((1:K) ⊗ₜ[R] s)) :=
      coextensionOriginalDualTensorEquiv_scalar_naturality s m _
    _ = coextensionOriginalDualTensorEquiv m (z*((1:K) ⊗ₜ[R] s)) := by rw [mul_assoc,hi]
    _ = _ := (coextensionOriginalDualTensorEquiv_scalar_naturality s m z).symm
/-- The actual fiber trace retains ORIGINAL eval-at-one on pure coefficients. -/
theorem coextensionOriginalFiberTrace_tmul (a : K) (ell : ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) :
    coextensionOriginalFiberTrace (a ⊗ₜ[R] ell)=
      a * algebraMap R K (coextensionOriginalEvaluationAtOne (R:=R) (S:=S)
        (show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from ell)) := by
  change coextensionOriginalDualTensorEquiv (a ⊗ₜ[R] ell) (1:(K ⊗[R] S))=_
  rw [Algebra.TensorProduct.one_def]
  exact coextensionOriginalDualTensorEquiv_original_evaluation a ell
/-- For any ORIGINAL scalar whose ACTUAL fiber class is a nonzero
idempotent,the SAME original scalar tensor endomorphism fixes a coefficient
on which the SAME actual fiber trace takes1. Finite/free input remains
EXPLICIT;original geometric freeness/Ext comparison/top-H calibration
and nonzero ORIGINAL geometric point weights are NOT asserted. -/
theorem coextensionOriginalFiberTrace_actual_point_exists_one
    (s : S) (he : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S)) ≠ 0)
    (hi : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S))*((1:K) ⊗ₜ[R] s)=((1:K) ⊗ₜ[R] s)) :
    ∃ m : (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))),coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s m=m ∧
      coextensionOriginalFiberTrace m=1 := by
  let e : (K ⊗[R] S) := (1:K) ⊗ₜ[R] s
  obtain ⟨eta,heta,htrace⟩ := coextensionFieldTrace_idempotent_fixed_exists_one
    (K:=K) e he hi
  let f : Module.Dual K (K ⊗[R] S) :=
    coextensionOriginalDualEquiv (R:=K) (S:=(K ⊗[R] S)) eta
  let m : (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) := (coextensionOriginalDualTensorEquiv (R:=R) (S:=S) (K:=K)).symm f
  have hm : coextensionOriginalDualTensorEquiv m=f :=
    (coextensionOriginalDualTensorEquiv (R:=R) (S:=S) (K:=K)).apply_symm_apply f
  refine ⟨m,?_,?_⟩
  · apply (coextensionOriginalDualTensorEquiv (R:=R) (S:=S) (K:=K)).injective
    apply LinearMap.ext
    intro z
    calc
      _ = coextensionOriginalDualTensorEquiv m (z*e) :=
        coextensionOriginalDualTensorEquiv_scalar_naturality s m z
      _ = f (z*e) := LinearMap.congr_fun hm _
      _ = (coextensionOriginalDualEquiv (R:=K) (S:=(K ⊗[R] S)) (e • eta)) z := by
        change eta (z*e)=(e • eta) z
        rw [ModuleCat.CoextendScalars.smul_apply]
      _ = f z := by rw [heta]
      _ = _ := (LinearMap.congr_fun hm z).symm
  · change coextensionOriginalDualTensorEquiv m (1:(K ⊗[R] S))=1
    rw [hm]
    exact htrace
end LinearStudy
