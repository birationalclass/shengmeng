module
public import Linear.CoextensionOriginalFiberPointProjector
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
variable {R S K : Type u} [CommRing R] [CommRing S] [Field K]
variable [Algebra R S] [Algebra R K] [Module.Free R S] [Module.Finite R S]
/-- Equality of ACTUAL fiber scalars gives equality of ORIGINAL scalar
tensor endomorphisms. No action is transported through the comparison. -/
theorem coextensionOriginalScalarFiberEnd_eq_of_fiber_eq
    (s t : S) (h : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S))=((1:K) ⊗ₜ[R] t)) :
    coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s=
      coextensionOriginalScalarFiberEnd (R:=R) (K:=K) t := by
  apply LinearMap.ext
  intro m
  apply (coextensionOriginalDualTensorEquiv (R:=R) (S:=S) (K:=K)).injective
  apply LinearMap.ext
  intro z
  rw [coextensionOriginalDualTensorEquiv_scalar_naturality,
    coextensionOriginalDualTensorEquiv_scalar_naturality,h]
/-- An ACTUAL residue-base surjection derives representatives of EVERY
fiber scalar. Choose a representative and use ORIGINAL S multiplication,
not multiplication transported through a duality isomorphism. Independence
of this representative is PROVED below. -/
def coextensionOriginalResidueFiberPointEnd
    (hres : Function.Surjective (algebraMap R K)) (e : (K ⊗[R] S)) :
    (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) →ₗ[K] (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) :=
  coextensionOriginalScalarFiberEnd (R:=R) (K:=K)
    (Classical.choose (Algebra.TensorProduct.includeRight_surjective
      (R:=R) (S:=K) (T:=S) hres e))
/-- The ACTUAL constructed endomorphism equals ORIGINAL multiplication
for EVERY representative,so its definition does not impose any desired law. -/
theorem coextensionOriginalResidueFiberPointEnd_of_lift
    (hres : Function.Surjective (algebraMap R K)) (e : (K ⊗[R] S))
    (s : S) (hs : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S))=e) :
    coextensionOriginalResidueFiberPointEnd hres e=
      coextensionOriginalScalarFiberEnd (R:=R) (K:=K) s := by
  unfold coextensionOriginalResidueFiberPointEnd
  apply coextensionOriginalScalarFiberEnd_eq_of_fiber_eq
  have hc := Classical.choose_spec (Algebra.TensorProduct.includeRight_surjective
    (R:=R) (S:=K) (T:=S) hres e)
  have hc' : ((1:K) ⊗ₜ[R] Classical.choose
      (Algebra.TensorProduct.includeRight_surjective (R:=R) (S:=K) (T:=S) hres e) : (K ⊗[R] S))=e := by
    simpa only [Algebra.TensorProduct.includeRight_apply] using hc
  exact hc'.trans hs.symm
/-- Every ACTUAL fiber idempotent gives an ACTUAL coefficient projector,
constructed by ORIGINAL source action. -/
theorem coextensionOriginalResidueFiberPointEnd_idempotent
    (hres : Function.Surjective (algebraMap R K)) (e : (K ⊗[R] S)) (hi : e*e=e) :
    ∀ m,coextensionOriginalResidueFiberPointEnd hres e
      (coextensionOriginalResidueFiberPointEnd hres e m)=
        coextensionOriginalResidueFiberPointEnd hres e m := by
  obtain ⟨s,hs⟩ := Algebra.TensorProduct.includeRight_surjective
    (R:=R) (S:=K) (T:=S) hres e
  have hs' : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S))=e := by
    simpa only [Algebra.TensorProduct.includeRight_apply] using hs
  rw [coextensionOriginalResidueFiberPointEnd_of_lift hres e s hs']
  exact coextensionOriginalScalarFiberEnd_idempotent s (by simpa only [hs'] using hi)
/-- The SAME ORIGINAL fiber trace takes1 on EVERY nonzero actual fiber
idempotent's ACTUAL original-action coefficient component. Finite/free and
residue-base surjectivity remain EXPLICIT algebraic hypotheses. Original
geometric local freeness,Ext comparison and top-H trace calibration are
NOT supplied;original geometric point weights/main remain OPEN. -/
theorem coextensionOriginalResidueFiberPointTrace_exists_one
    (hres : Function.Surjective (algebraMap R K)) (e : (K ⊗[R] S))
    (he : e ≠ 0) (hi : e*e=e) :
    ∃ m : (K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))),coextensionOriginalResidueFiberPointEnd hres e m=m ∧
      coextensionOriginalFiberTrace (R:=R) (S:=S) (K:=K) m=1 := by
  obtain ⟨s,hs⟩ := Algebra.TensorProduct.includeRight_surjective
    (R:=R) (S:=K) (T:=S) hres e
  have hs' : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S))=e := by
    simpa only [Algebra.TensorProduct.includeRight_apply] using hs
  have hsne : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S)) ≠ 0 := by simpa only [hs'] using he
  have hsi : ((1:K) ⊗ₜ[R] s : (K ⊗[R] S))*((1:K) ⊗ₜ[R] s)=((1:K) ⊗ₜ[R] s) := by
    simpa only [hs'] using hi
  obtain ⟨m,hm,ht⟩ := coextensionOriginalFiberTrace_actual_point_exists_one s hsne hsi
  refine ⟨m,?_,ht⟩
  rw [coextensionOriginalResidueFiberPointEnd_of_lift hres e s hs']
  exact hm
end LinearStudy
