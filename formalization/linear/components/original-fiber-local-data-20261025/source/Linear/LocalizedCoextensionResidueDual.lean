module
public import Linear.AbstractLocalizedModuleResidueFiber
public import Linear.NativeCoextensionLocalizedTarget
public import Linear.CoextensionOriginalDualTensorBaseChange
public import Mathlib.RingTheory.Localization.Finiteness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
variable {R S Q K : Type u} [CommRing R] [CommRing S] [CommRing Q] [CommRing K]
variable [Algebra R S] [Algebra R Q] [Algebra R K] [Algebra Q K]
variable [IsScalarTower R Q K] [Module.Finite R S]
variable (P : Submonoid R) [IsLocalization P Q]
variable (hfree : letI : Module Q (LocalizedModule P S) := LocalizedModule.moduleOfIsLocalization
  Module.Free Q (LocalizedModule P S))
/-- ACTUAL original coextension fiber dual comparison under ONLY LOCAL
freeness of the actual localized source. Original S/R is NOT assumed free.
All localization actions are mathlib's actual original ones,never defined
by transport through this comparison. -/
def localizedCoextensionOriginalDualTensorEquiv
    (hinj : Function.Injective (algebraMap R Q)) :
    K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) ≃ₗ[K]
        Module.Dual K (K ⊗[R] S) := by
  let S' := LocalizedModule P S
  let C := (ModuleCat.restrictScalars (algebraMap R S)).obj
    ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))
  letI : Module Q (LocalizedModule P ((ModuleCat.restrictScalars (algebraMap R S)).obj
    ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) :=
      LocalizedModule.moduleOfIsLocalization
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S:=P) Q
  letI : Module.Free Q S' := hfree
  letI : Module.Finite Q S' := Module.Finite.of_isLocalizedModule P (Rₚ:=Q)
    (LocalizedModule.mkLinearMap P S)
  let alpha := finiteNativeCoextensionLocalizedTargetEquiv (R:=R) (S:=S) P hinj
  exact (abstractLocalizedModuleFiberEquiv (Q:=Q) P C).symm ≪≫ₗ
    (alpha.baseChange Q K _ _) ≪≫ₗ
    coextensionOriginalDualTensorEquiv (R:=Q) (S:=S') (K:=K) ≪≫ₗ
    Module.Dual.congr (abstractLocalizedModuleFiberEquiv (Q:=Q) P S)
/-- The LOCAL comparison retains every ORIGINAL functional value on
actual pure tensors;no desired trace identity is an input. -/
theorem localizedCoextensionOriginalDualTensorEquiv_tmul_apply
    (hinj : Function.Injective (algebraMap R Q)) (a : K)
    (ell : (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) (s : S) :
    localizedCoextensionOriginalDualTensorEquiv P hfree hinj (a ⊗ₜ[R] ell) ((1:K) ⊗ₜ[R] s)=
      a * algebraMap R K ((coextensionOriginalDualEquiv (R:=R) (S:=S) ell) s) := by
  let S' := LocalizedModule P S
  letI : Module Q (LocalizedModule P ((ModuleCat.restrictScalars (algebraMap R S)).obj
    ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))) :=
      LocalizedModule.moduleOfIsLocalization
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S:=P) Q
  letI : Module.Free Q S' := hfree
  letI : Module.Finite Q S' := Module.Finite.of_isLocalizedModule P (Rₚ:=Q)
    (LocalizedModule.mkLinearMap P S)
  simp only [localizedCoextensionOriginalDualTensorEquiv,LinearEquiv.trans_apply,
    abstractLocalizedModuleFiberEquiv_symm_tmul,LinearEquiv.baseChange_tmul]
  change coextensionOriginalDualTensorEquiv
    (a ⊗ₜ[Q] (finiteNativeCoextensionLocalizedTargetEquiv (R:=R) (S:=S) P hinj
      (LocalizedModule.mk ell 1)))
    ((abstractLocalizedModuleFiberEquiv (Q:=Q) P S).symm ((1:K) ⊗ₜ[R] s))=_
  rw [abstractLocalizedModuleFiberEquiv_symm_tmul,
    coextensionOriginalDualTensorEquiv_tmul_apply]
  change a * algebraMap Q K
    (nativeCoextensionOriginalDualEquiv (R:=Q) (S:=S')
      (finiteNativeCoextensionLocalizedTargetEquiv (R:=R) (S:=S) P hinj
        (LocalizedModule.mk ell 1)) (LocalizedModule.mk s 1))=_
  rw [finiteNativeCoextensionLocalizedTargetEquiv_apply_original]
  rw [← IsScalarTower.algebraMap_apply R Q K]
  rfl
/-- Original evaluation at the ACTUAL fiber unit is retained even though
freeness is imposed ONLY after the actual base localization. -/
theorem localizedCoextensionOriginalDualTensorEquiv_original_evaluation
    (hinj : Function.Injective (algebraMap R Q)) (a : K)
    (ell : (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) :
    localizedCoextensionOriginalDualTensorEquiv P hfree hinj (a ⊗ₜ[R] ell) ((1:K) ⊗ₜ[R] (1:S))=
      a * algebraMap R K (coextensionOriginalEvaluationAtOne (R:=R) (S:=S)
        (show (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) from ell)) := by
  exact localizedCoextensionOriginalDualTensorEquiv_tmul_apply P hfree hinj a ell (1:S)
end LinearStudy
