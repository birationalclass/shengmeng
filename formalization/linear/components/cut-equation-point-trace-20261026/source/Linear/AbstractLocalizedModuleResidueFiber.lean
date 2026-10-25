module
public import Linear.LocalizedModuleResidueFiber
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open TensorProduct
universe u v
variable {R Q K : Type u} [CommRing R] [CommRing Q] [CommRing K]
variable [Algebra R Q] [Algebra R K] [Algebra Q K] [IsScalarTower R Q K]
variable (P : Submonoid R) [IsLocalization P Q]
variable (M : Type v) [AddCommGroup M] [Module R M]
/-- ACTUAL module fiber comparison for an arbitrary actual base
localization,with mathlib original abstract-localization scalar action.
No action is defined by transport through this comparison. -/
def abstractLocalizedModuleFiberEquiv :
    letI : Module Q (LocalizedModule P M) := LocalizedModule.moduleOfIsLocalization
    K ⊗[Q] LocalizedModule P M ≃ₗ[K] K ⊗[R] M := by
  letI : Module Q (LocalizedModule P M) := LocalizedModule.moduleOfIsLocalization
  let e : Q ⊗[R] M ≃ₗ[Q] LocalizedModule P M :=
    (IsLocalizedModule.isBaseChange P Q (LocalizedModule.mkLinearMap P M)).equiv
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e.symm).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R Q K K M)
/-- ORIGINAL numerator tensors are preserved by the actual comparison. -/
theorem abstractLocalizedModuleFiberEquiv_tmul (a : K) (m : M) :
    letI : Module Q (LocalizedModule P M) := LocalizedModule.moduleOfIsLocalization
    abstractLocalizedModuleFiberEquiv (Q:=Q) P M (a ⊗ₜ[Q] LocalizedModule.mk m 1)=
      a ⊗ₜ[R] m := by
  letI : Module Q (LocalizedModule P M) := LocalizedModule.moduleOfIsLocalization
  let e : Q ⊗[R] M ≃ₗ[Q] LocalizedModule P M :=
    (IsLocalizedModule.isBaseChange P Q (LocalizedModule.mkLinearMap P M)).equiv
  have he : e ((1:Q) ⊗ₜ[R] m)=LocalizedModule.mk m 1 := by
    simp [e,IsBaseChange.equiv_tmul]
  have hes : e.symm (LocalizedModule.mk m 1)=((1:Q) ⊗ₜ[R] m) :=
    e.symm_apply_eq.mpr he.symm
  change TensorProduct.AlgebraTensorModule.cancelBaseChange R Q K K M
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e.symm)
      (a ⊗ₜ[Q] LocalizedModule.mk m 1))=_
  rw [TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,hes,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,one_smul]
/-- The inverse uses the SAME original numerator. -/
theorem abstractLocalizedModuleFiberEquiv_symm_tmul (a : K) (m : M) :
    letI : Module Q (LocalizedModule P M) := LocalizedModule.moduleOfIsLocalization
    (abstractLocalizedModuleFiberEquiv (Q:=Q) P M).symm (a ⊗ₜ[R] m)=
      a ⊗ₜ[Q] LocalizedModule.mk m 1 := by
  letI : Module Q (LocalizedModule P M) := LocalizedModule.moduleOfIsLocalization
  apply (abstractLocalizedModuleFiberEquiv (Q:=Q) P M).injective
  rw [LinearEquiv.apply_symm_apply,abstractLocalizedModuleFiberEquiv_tmul]
end LinearStudy
