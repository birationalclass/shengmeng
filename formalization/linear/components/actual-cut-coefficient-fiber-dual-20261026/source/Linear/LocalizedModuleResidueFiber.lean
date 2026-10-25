module
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open TensorProduct
universe u v
variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
variable (P : Submonoid R) [Algebra (Localization P) K] [IsScalarTower R (Localization P) K]
variable (M : Type v) [AddCommGroup M] [Module R M]
/-- ACTUAL module localization followed by the SAME residue base change
is the original module fiber. No freeness or flatness hypothesis. -/
def originalLocalizedModuleFiberEquiv :
    K ⊗[Localization P] LocalizedModule P M ≃ₗ[K] K ⊗[R] M :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
    (LocalizedModule.equivTensorProduct P M)).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization P) K K M)
/-- The comparison preserves ORIGINAL pure numerator tensors. -/
theorem originalLocalizedModuleFiberEquiv_tmul (a : K) (m : M) :
    originalLocalizedModuleFiberEquiv P M (a ⊗ₜ[Localization P] LocalizedModule.mk m 1)=
      a ⊗ₜ[R] m := by
  simp [originalLocalizedModuleFiberEquiv,LocalizedModule.equivTensorProduct_apply_mk,
    Localization.mk_one_eq_algebraMap]
/-- The inverse has the ACTUAL numerator representative. -/
theorem originalLocalizedModuleFiberEquiv_symm_tmul (a : K) (m : M) :
    (originalLocalizedModuleFiberEquiv P M).symm (a ⊗ₜ[R] m)=
      a ⊗ₜ[Localization P] LocalizedModule.mk m 1 := by
  apply (originalLocalizedModuleFiberEquiv P M).injective
  rw [LinearEquiv.apply_symm_apply,originalLocalizedModuleFiberEquiv_tmul]
end LinearStudy
