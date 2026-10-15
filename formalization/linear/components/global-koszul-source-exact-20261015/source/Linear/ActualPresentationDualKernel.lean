module
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Isomorphisms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {S R E M : Type*} [CommRing S]
variable [AddCommGroup R] [Module S R] [AddCommGroup E] [Module S E]
variable [AddCommGroup M] [Module S M]
variable (c : R →ₗ[S] E) (b : E →ₗ[S] M)
variable (hb : Function.Surjective b) (h : LinearMap.range c = LinearMap.ker b)

/-- For the ACTUAL original presentation R->E->M->0, precomposition
with its actual quotient b identifies Hom_S(M,S) with the kernel of
its actual dual relation c*. This reuses mathlib's quotient-dual and
annihilator equivalences; neither relation injectivity nor freeness
nor a field hypothesis on S is assumed. -/
def actualPresentationDualKernelEquiv :
    Module.Dual S M ≃ₗ[S] LinearMap.ker c.dualMap :=
  ((Submodule.quotEquivOfEq (LinearMap.range c) (LinearMap.ker b) h).trans
    (b.quotKerEquivOfSurjective hb)).dualMap |>.trans
    (Submodule.dualQuotEquivDualAnnihilator (LinearMap.range c)) |>.trans
      (LinearEquiv.ofEq (LinearMap.range c).dualAnnihilator
        (LinearMap.ker c.dualMap) c.ker_dualMap_eq_dualAnnihilator_range.symm)

/-- The constructed equivalence is precisely precomposition with the
original quotient map on EVERY original argument, not an arbitrary
abstract isomorphism of modules. -/
theorem actualPresentationDualKernelEquiv_apply (φ : Module.Dual S M) (x : E) :
    (actualPresentationDualKernelEquiv c b hb h φ).1 x = φ (b x) := by
  rfl

end LinearStudy
