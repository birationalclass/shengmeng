module
public import Linear.NativeDualLocalizationFractionValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S Q : Type u} [CommRing R] [CommRing S] [CommRing Q]
variable [Algebra R S] [Algebra R Q] [Module.Finite R S]
variable (P : Submonoid R) [IsLocalization P Q]
attribute [local instance] LocalizedModule.moduleOfIsLocalization
@[reducible] def actualRestrictedNativeDual :=
  ((ModuleCat.restrictScalars (algebraMap R S)).obj
    ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))
/-- The ORIGINAL upper-ring action on the native dual, retained as an R-linear endomorphism. -/
def nativeDualUpperMultiplication (s : S) :
    actualRestrictedNativeDual (R:=R) (S:=S) →ₗ[R] actualRestrictedNativeDual (R:=R) (S:=S) where
  toFun ell := s • (show (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) from ell)
  map_add' ell k := smul_add s ell k
  map_smul' r ell := by
    apply (nativeCoextensionOriginalDualEquiv (R:=R) (S:=S)).injective
    ext x
    change nativeCoextensionOriginalDualEquiv ell ((x*s)*algebraMap R S r) =
      nativeCoextensionOriginalDualEquiv ell ((x*algebraMap R S r)*s)
    congr 1
    ring
/-- Evaluation intertwines original source multiplication with precomposition. -/
theorem nativeDualUpperMultiplication_eval (s x : S)
    (ell : actualRestrictedNativeDual (R:=R) (S:=S)) :
    nativeCoextensionOriginalDualEquiv (nativeDualUpperMultiplication s ell) x =
      nativeCoextensionOriginalDualEquiv ell (x*s) := by
  rfl
/-- The actual universal localization of this original multiplication map. -/
def nativeDualLocalizedUpperMultiplication (s : S) :=
  IsLocalizedModule.map P
    (LocalizedModule.mkLinearMap P (actualRestrictedNativeDual (R:=R) (S:=S)))
    (LocalizedModule.mkLinearMap P (actualRestrictedNativeDual (R:=R) (S:=S)))
    (nativeDualUpperMultiplication (R:=R) s)
/-- On ALL actual localized source fractions, evaluation obeys the ORIGINAL upper-ring action. -/
theorem nativeDualLocalizedUpperMultiplication_eval
    (hinj : Function.Injective (algebraMap R Q)) (s : S)
    (ell : actualRestrictedNativeDual (R:=R) (S:=S)) (x : S) (p q : P) :
    finiteNativeCoextensionLocalizationEquiv P hinj
      (nativeDualLocalizedUpperMultiplication P s (LocalizedModule.mk ell p))
      (LocalizedModule.mk x q) =
    finiteNativeCoextensionLocalizationEquiv P hinj (LocalizedModule.mk ell p)
      (LocalizedModule.mk (x*s) q) := by
  rw [nativeDualLocalizedUpperMultiplication,IsLocalizedModule.map_LocalizedModules]
  rw [finiteNativeCoextensionLocalizationEquiv_apply_fraction,
    finiteNativeCoextensionLocalizationEquiv_apply_fraction,nativeDualUpperMultiplication_eval]
/-- Every actual localized dual/source pair respects original upper-ring multiplication. -/
theorem nativeDualLocalizedUpperMultiplication_eval_all
    (hinj : Function.Injective (algebraMap R Q)) (s : S)
    (ell : LocalizedModule P (actualRestrictedNativeDual (R:=R) (S:=S)))
    (x : LocalizedModule P S) :
    finiteNativeCoextensionLocalizationEquiv P hinj
      (nativeDualLocalizedUpperMultiplication P s ell) x =
      finiteNativeCoextensionLocalizationEquiv P hinj ell
        (x * LocalizedModule.mk s 1) := by
  induction ell using LocalizedModule.induction_on with
  | _ m p =>
    induction x using LocalizedModule.induction_on with
    | _ y q =>
      rw [LocalizedModule.mk_mul_mk, mul_one]
      exact nativeDualLocalizedUpperMultiplication_eval P hinj s m y p q
/-- All localized source fractions act by the actual localized upper-ring map and inverse base denominator. -/
theorem nativeDualLocalizedSourceFraction_eval
    (hinj : Function.Injective (algebraMap R Q)) (s : S) (t : P)
    (ell : LocalizedModule P (actualRestrictedNativeDual (R:=R) (S:=S)))
    (x : LocalizedModule P S) :
    finiteNativeCoextensionLocalizationEquiv P hinj
      (IsLocalization.mk' Q 1 t • nativeDualLocalizedUpperMultiplication P s ell) x =
      finiteNativeCoextensionLocalizationEquiv P hinj ell
        (x * LocalizedModule.mk s t) := by
  rw [map_smul, LinearMap.smul_apply]
  induction ell using LocalizedModule.induction_on with
  | _ m p =>
    induction x using LocalizedModule.induction_on with
    | _ y q =>
      rw [nativeDualLocalizedUpperMultiplication_eval,
        LocalizedModule.mk_mul_mk,
        finiteNativeCoextensionLocalizationEquiv_apply_fraction,
        finiteNativeCoextensionLocalizationEquiv_apply_fraction]
      rw [smul_eq_mul, ← IsLocalization.mk'_mul, one_mul]
      congr 1
      ac_rfl
end LinearStudy
