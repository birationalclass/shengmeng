module
public import Linear.FiniteNativeCoextensionLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S Q : Type u} [CommRing R] [CommRing S] [CommRing Q]
variable [Algebra R S] [Algebra R Q] [Module.Finite R S]
variable (P : Submonoid R) [IsLocalization P Q]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- Explicit evaluation of two ACTUAL native dual/source fractions. -/
theorem finiteNativeCoextensionLocalizationEquiv_apply_fraction
    (hinj : Function.Injective (algebraMap R Q))
    (ell : (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))
    (x : S) (s t : P) :
    finiteNativeCoextensionLocalizationEquiv P hinj (LocalizedModule.mk ell s)
      (LocalizedModule.mk x t) =
      IsLocalization.mk' Q (nativeCoextensionOriginalDualEquiv ell x) (s*t) := by
  let e := finiteNativeCoextensionLocalizationEquiv (S := S) P hinj
  have hs : (s : R) • LocalizedModule.mk ell s = LocalizedModule.mk ell 1 := by
    simpa only [LocalizedModule.smul'_mk, Submonoid.smul_def] using
      LocalizedModule.mk_cancel s ell
  have ht : (t : R) • LocalizedModule.mk x t = LocalizedModule.mk x 1 := by
    simpa only [LocalizedModule.smul'_mk, Submonoid.smul_def] using
      LocalizedModule.mk_cancel t x
  have hcalc : e ((s : R) • LocalizedModule.mk ell s)
      ((t : R) • LocalizedModule.mk x t) =
        algebraMap R Q ((s : R)*(t : R)) *
          e (LocalizedModule.mk ell s) (LocalizedModule.mk x t) := by
    have he : e ((s : R) • LocalizedModule.mk ell s) =
        (s : R) • e (LocalizedModule.mk ell s) := by
      simpa only [IsScalarTower.algebraMap_smul] using
        e.map_smul (algebraMap R Q (s : R)) (LocalizedModule.mk ell s)
    have hf : e (LocalizedModule.mk ell s) ((t : R) • LocalizedModule.mk x t) =
        (t : R) • e (LocalizedModule.mk ell s) (LocalizedModule.mk x t) := by
      simpa only [IsScalarTower.algebraMap_smul] using
        (e (LocalizedModule.mk ell s)).map_smul (algebraMap R Q (t : R))
          (LocalizedModule.mk x t)
    rw [he, LinearMap.smul_apply, hf]
    simp only [Algebra.smul_def, map_mul, mul_assoc]
  have hclear : algebraMap R Q ((s : R)*(t : R)) *
      e (LocalizedModule.mk ell s) (LocalizedModule.mk x t) =
        algebraMap R Q (nativeCoextensionOriginalDualEquiv ell x) := by
    rw [← hcalc, hs, ht]
    exact finiteNativeCoextensionLocalizationEquiv_apply_mk P hinj ell x
  apply (IsLocalization.map_units Q (s*t)).mul_left_cancel
  exact hclear.trans
    (IsLocalization.mk'_spec' Q (nativeCoextensionOriginalDualEquiv ell x) (s*t)).symm

end LinearStudy
