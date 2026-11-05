module
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Abelian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe u
variable {K A B : Type u} [Field K] [AddCommGroup A] [Module K A]
variable [AddCommGroup B] [Module K B] (δ : B →ₗ[K] A)

/-- The actual vector-space quotient by im(delta*) is canonically
Dual(ker delta),using mathlib's original range/annihilator and quotient
restriction equivalences. No finite-dimensional hypothesis is needed. -/
def vectorDualCokernelKernelEquiv :
    (Module.Dual K B ⧸ LinearMap.range δ.dualMap) ≃ₗ[K] Module.Dual K (LinearMap.ker δ) :=
  (Submodule.quotEquivOfEq (LinearMap.range δ.dualMap) (LinearMap.ker δ).dualAnnihilator
    δ.range_dualMap_eq_dualAnnihilator_ker).trans
      (Subspace.quotAnnihilatorEquiv (LinearMap.ker δ))

/-- The original quotient functional is sent to its ORIGINAL restriction
on the actual kernel,not an arbitrary chosen duality map. -/
theorem vectorDualCokernelKernelEquiv_apply (φ : Module.Dual K B) (x : LinearMap.ker δ) :
    vectorDualCokernelKernelEquiv δ (Submodule.Quotient.mk φ) x = φ x.1 := by
  simp only [vectorDualCokernelKernelEquiv,LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk,Subspace.quotAnnihilatorEquiv_apply]
  rfl

/-- The ACTUAL categorical cokernel of delta* is the dual of the
ACTUAL delta kernel,using the original categorical quotient comparison. -/
def vectorDualCokernelKernelIso :
    cokernel (ModuleCat.ofHom δ.dualMap) ≅ ModuleCat.of K (Module.Dual K (LinearMap.ker δ)) :=
  (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom δ.dualMap)).trans
    (vectorDualCokernelKernelEquiv δ).toModuleIso

/-- The categorical comparison respects the ORIGINAL cokernel quotient
and ORIGINAL kernel restriction. This is the required quotient square. -/
theorem vectorDualCokernelKernelIso_quotient :
    cokernel.π (ModuleCat.ofHom δ.dualMap) ≫ (vectorDualCokernelKernelIso δ).hom =
    ModuleCat.ofHom (LinearMap.ker δ).dualRestrict := by
  unfold vectorDualCokernelKernelIso
  rw [Iso.trans_hom,← Category.assoc,ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  exact vectorDualCokernelKernelEquiv_apply δ φ x

end LinearStudy
