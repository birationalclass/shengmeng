module
public import Linear.LocalizedCoextensionResidueDual
public import Linear.CoextensionTensorEvaluation
public import Linear.CoextensionResidueFiberPointProjector
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
variable {R S Q K : Type u} [CommRing R] [CommRing S] [CommRing Q] [Field K]
variable [Algebra R S] [Algebra R Q] [Algebra R K] [Algebra Q K]
variable [IsScalarTower R Q K] [Module.Finite R S]
variable (P : Submonoid R) [IsLocalization P Q]
variable (hfree : letI : Module Q (LocalizedModule P S) := LocalizedModule.moduleOfIsLocalization
  Module.Free Q (LocalizedModule P S))
variable (hinj : Function.Injective (algebraMap R Q))
include P hfree hinj
attribute [local irreducible] localizedCoextensionOriginalDualTensorEquiv
/-- The actual local dual comparison evaluates at the unit by the
LITERAL base change of ORIGINAL eval1. The functional is independent of
this comparison and of every freeness choice. -/
theorem localizedCoextensionOriginalDualTensorEquiv_evaluation
    (m : K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) :
    localizedCoextensionOriginalDualTensorEquiv P hfree hinj m (1:(K ⊗[R] S))=
      coextensionOriginalBaseChangedEvaluationAtOne m := by
  induction m using TensorProduct.inductionOn with
  | tmul a ell =>
    rw [Algebra.TensorProduct.one_def,
      localizedCoextensionOriginalDualTensorEquiv_original_evaluation,
      coextensionOriginalBaseChangedEvaluationAtOne_tmul]
  | add m n hm hn => simp only [map_add,LinearMap.add_apply,hm,hn]
/-! ONLY the ACTUAL localized algebra is assumed free. The ORIGINAL
source action and existing actual point-projector object are retained.
No global S/R freeness,no replacement trace and no geometric top-H
calibration are assumed or asserted. -/
theorem localizedCoextensionOriginalDualTensorEquiv_both_tmul
    (a b : K) (ell : ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) (t : S) :
    localizedCoextensionOriginalDualTensorEquiv P hfree hinj (a ⊗ₜ[R] ell) (b ⊗ₜ[R] t)=
      b * (a * algebraMap R K ((coextensionOriginalDualEquiv (R:=R) (S:=S) ell) t)) := by
  calc
    _ = localizedCoextensionOriginalDualTensorEquiv P hfree hinj (a ⊗ₜ[R] ell)
        (b • ((1:K) ⊗ₜ[R] t)) := by
      rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    _ = b * localizedCoextensionOriginalDualTensorEquiv P hfree hinj (a ⊗ₜ[R] ell) ((1:K) ⊗ₜ[R] t) := by
      rw [map_smul,smul_eq_mul]
    _ = _ := by rw [localizedCoextensionOriginalDualTensorEquiv_tmul_apply P hfree hinj]

theorem localizedCoextensionOriginalDualTensorEquiv_scalar_naturality
    (s : S) (m : (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))))) (z : (K ⊗[R] S)) :
    localizedCoextensionOriginalDualTensorEquiv P hfree hinj
        (coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s m) z=
      localizedCoextensionOriginalDualTensorEquiv P hfree hinj m (z*((1:K) ⊗ₜ[R] s)) := by
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => simp only [map_add,LinearMap.add_apply,hm,hn]
  | tmul a ell =>
    change localizedCoextensionOriginalDualTensorEquiv P hfree hinj
      (a ⊗ₜ[R] (show ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) from s • (show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from ell))) z=
        localizedCoextensionOriginalDualTensorEquiv P hfree hinj (a ⊗ₜ[R] ell) (z*((1:K) ⊗ₜ[R] s))
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [add_mul,map_add,hz,hw]
    | tmul b t =>
      rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one]
      rw [localizedCoextensionOriginalDualTensorEquiv_both_tmul P hfree hinj,
        localizedCoextensionOriginalDualTensorEquiv_both_tmul P hfree hinj]
      change b * (a * algebraMap R K ((s • (show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from ell)) t))=
        b * (a * algebraMap R K ((show ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) from ell) (t*s)))
      rw [ModuleCat.CoextendScalars.smul_apply]

theorem localizedCoextensionOriginalScalarFiberEnd_idempotent (s : S)
    (hi : ((1:K) ⊗ₜ[R] s : K ⊗[R] S)*((1:K) ⊗ₜ[R] s)=((1:K) ⊗ₜ[R] s)) :
    ∀ m,coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s
      (coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s m)=
        coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s m := by
  intro m
  apply (localizedCoextensionOriginalDualTensorEquiv (R:=R) (S:=S) (Q:=Q) (K:=K) P hfree hinj).injective
  apply LinearMap.ext
  intro z
  calc
    _ = localizedCoextensionOriginalDualTensorEquiv P hfree hinj
        (coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s m) (z*((1:K) ⊗ₜ[R] s)) :=
      localizedCoextensionOriginalDualTensorEquiv_scalar_naturality P hfree hinj s _ z
    _ = localizedCoextensionOriginalDualTensorEquiv P hfree hinj m ((z*((1:K) ⊗ₜ[R] s))*((1:K) ⊗ₜ[R] s)) :=
      localizedCoextensionOriginalDualTensorEquiv_scalar_naturality P hfree hinj s m _
    _ = localizedCoextensionOriginalDualTensorEquiv P hfree hinj m (z*((1:K) ⊗ₜ[R] s)) := by rw [mul_assoc,hi]
    _ = _ := (localizedCoextensionOriginalDualTensorEquiv_scalar_naturality P hfree hinj s m z).symm

theorem localizedCoextensionOriginalFiberTrace_actual_point_exists_one
    (s : S) (he : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S)) ≠ 0)
    (hi : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S))*((1:K) ⊗ₜ[R] s)=((1:K) ⊗ₜ[R] s)) :
    ∃ m : (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))),coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s m=m ∧
      coextensionOriginalBaseChangedEvaluationAtOne m=1 := by
  let e : (K ⊗[R] S) := (1:K) ⊗ₜ[R] s
  obtain ⟨eta,heta,htrace⟩ := coextensionFieldTrace_idempotent_fixed_exists_one
    (K:=K) e he hi
  let f : Module.Dual K (K ⊗[R] S) :=
    coextensionOriginalDualEquiv (R:=K) (S:=(K ⊗[R] S)) eta
  let m : (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) := (localizedCoextensionOriginalDualTensorEquiv (R:=R) (S:=S) (Q:=Q) (K:=K) P hfree hinj).symm f
  have hm : localizedCoextensionOriginalDualTensorEquiv P hfree hinj m=f :=
    (localizedCoextensionOriginalDualTensorEquiv (R:=R) (S:=S) (Q:=Q) (K:=K) P hfree hinj).apply_symm_apply f
  refine ⟨m,?_,?_⟩
  · apply (localizedCoextensionOriginalDualTensorEquiv (R:=R) (S:=S) (Q:=Q) (K:=K) P hfree hinj).injective
    apply LinearMap.ext
    intro z
    calc
      _ = localizedCoextensionOriginalDualTensorEquiv P hfree hinj m (z*e) :=
        localizedCoextensionOriginalDualTensorEquiv_scalar_naturality P hfree hinj s m z
      _ = f (z*e) := LinearMap.congr_fun hm _
      _ = (coextensionOriginalDualEquiv (R:=K) (S:=(K ⊗[R] S)) (e • eta)) z := by
        change eta (z*e)=(e • eta) z
        rw [ModuleCat.CoextendScalars.smul_apply]
      _ = f z := by rw [heta]
      _ = _ := (LinearMap.congr_fun hm z).symm
  · rw [← localizedCoextensionOriginalDualTensorEquiv_evaluation P hfree hinj]
    rw [hm]
    exact htrace

theorem localizedCoextensionOriginalScalarFiberEnd_eq_of_fiber_eq
    (s t : S) (h : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S))=((1:K) ⊗ₜ[R] t)) :
    coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s=
      coextensionOriginalScalarFiberEnd (R:=R) (K:=K) t := by
  apply LinearMap.ext
  intro m
  apply (localizedCoextensionOriginalDualTensorEquiv (R:=R) (S:=S) (Q:=Q) (K:=K) P hfree hinj).injective
  apply LinearMap.ext
  intro z
  rw [localizedCoextensionOriginalDualTensorEquiv_scalar_naturality P hfree hinj,
    localizedCoextensionOriginalDualTensorEquiv_scalar_naturality P hfree hinj,h]
theorem localizedCoextensionOriginalResidueFiberPointEnd_of_lift
    (hres : Function.Surjective (algebraMap R K)) (e : (K ⊗[R] S))
    (s : S) (hs : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S))=e) :
    coextensionOriginalResidueFiberPointEnd hres e=
      coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s := by
  unfold coextensionOriginalResidueFiberPointEnd
  apply localizedCoextensionOriginalScalarFiberEnd_eq_of_fiber_eq P hfree hinj
  have hc := Classical.choose_spec (Algebra.TensorProduct.includeRight_surjective
    (R:=R) (S:=K) (T:=S) hres e)
  have hc' : ((1:K) ⊗ₜ[R] Classical.choose
      (Algebra.TensorProduct.includeRight_surjective (R:=R) (S:=K) (T:=S) hres e) : (K ⊗[R] S))=e := by
    simpa only [Algebra.TensorProduct.includeRight_apply] using hc
  exact hc'.trans hs.symm

theorem localizedCoextensionOriginalResidueFiberPointEnd_idempotent
    (hres : Function.Surjective (algebraMap R K)) (e : (K ⊗[R] S)) (hi : e*e=e) :
    ∀ m,coextensionOriginalResidueFiberPointEnd hres e
      (coextensionOriginalResidueFiberPointEnd hres e m)=
        coextensionOriginalResidueFiberPointEnd hres e m := by
  obtain ⟨s,hs⟩ := Algebra.TensorProduct.includeRight_surjective
    (R:=R) (S:=K) (T:=S) hres e
  have hs' : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S))=e := by
    simpa only [Algebra.TensorProduct.includeRight_apply] using hs
  rw [localizedCoextensionOriginalResidueFiberPointEnd_of_lift P hfree hinj hres e s hs']
  exact localizedCoextensionOriginalScalarFiberEnd_idempotent P hfree hinj s (by simpa only [hs'] using hi)

theorem localizedCoextensionOriginalResidueFiberPointTrace_exists_one
    (hres : Function.Surjective (algebraMap R K)) (e : (K ⊗[R] S))
    (he : e ≠ 0) (hi : e*e=e) :
    ∃ m : (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))),coextensionOriginalResidueFiberPointEnd hres e m=m ∧
      coextensionOriginalBaseChangedEvaluationAtOne (R:=R) (S:=S) (K:=K) m=1 := by
  obtain ⟨s,hs⟩ := Algebra.TensorProduct.includeRight_surjective
    (R:=R) (S:=K) (T:=S) hres e
  have hs' : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S))=e := by
    simpa only [Algebra.TensorProduct.includeRight_apply] using hs
  have hsne : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S)) ≠ 0 := by simpa only [hs'] using he
  have hsi : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S))*((1:K) ⊗ₜ[R] s)=((1:K) ⊗ₜ[R] s) := by
    simpa only [hs'] using hi
  obtain ⟨m,hm,ht⟩ := localizedCoextensionOriginalFiberTrace_actual_point_exists_one P hfree hinj s hsne hsi
  refine ⟨m,?_,ht⟩
  rw [localizedCoextensionOriginalResidueFiberPointEnd_of_lift P hfree hinj hres e s hs']
  exact hm
end LinearStudy
