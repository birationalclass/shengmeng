module
public import Linear.FiniteFunctionalLocalizationEquiv
public import Linear.FiniteCoextensionModule
public import Mathlib.LinearAlgebra.Dual.BaseChange
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

/-- Compare the actual restricted native coextension with the ordinary
dual of the original algebra carrier, retaining both scalar comparisons. -/
def nativeCoextensionOriginalDualEquiv :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) ≃ₗ[R]
      (S →ₗ[R] R) :=
  restrictedCoextensionDualEquiv.trans (Module.Dual.congr restrictedAlgebraModuleEquiv)

/-- The actual codomain-localization map on native coextension. -/
def nativeCoextensionFunctionalLocalizationMap :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) →ₗ[R]
      (S →ₗ[R] Q) :=
  (LinearMap.compRight (M := S) R (Algebra.linearMap R Q)).comp
    (nativeCoextensionOriginalDualEquiv (R := R) (S := S)).toLinearMap

/-- This actual map is a module localization for a finite original algebra;
the algebra need not be free over the normalization base. -/
theorem nativeCoextensionFunctionalLocalizationMap_isLocalizedModule
    (hinj : Function.Injective (algebraMap R Q)) :
    IsLocalizedModule P (nativeCoextensionFunctionalLocalizationMap (R := R) (S := S) (Q := Q)) := by
  let j := LinearMap.compRight (M := S) R (Algebra.linearMap R Q)
  letI : IsLocalizedModule P j :=
    finiteLinearFunctional_compRight_isLocalizedModule P hinj
  exact IsLocalizedModule.of_linearEquiv_right P j
    (nativeCoextensionOriginalDualEquiv (R := R) (S := S))

/-- The ACTUAL localized native coextension is compared with the actual
localized-algebra source dual, not a supplied canonical module. -/
def finiteNativeCoextensionLocalizationEquiv
    (hinj : Function.Injective (algebraMap R Q)) :
    LocalizedModule P ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) ≃ₗ[Q]
      (LocalizedModule P S →ₗ[Q] Q) := by
  let j := nativeCoextensionFunctionalLocalizationMap (R := R) (S := S) (Q := Q)
  letI : IsLocalizedModule P j :=
    nativeCoextensionFunctionalLocalizationMap_isLocalizedModule (S := S) P hinj
  exact ((IsLocalizedModule.iso P j).extendScalarsOfIsLocalization P Q).trans
    (functionalSourceLocalizationEquiv P)

theorem finiteNativeCoextensionLocalizationEquiv_apply_mk
    (hinj : Function.Injective (algebraMap R Q))
    (ell : (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) (x : S) :
    finiteNativeCoextensionLocalizationEquiv P hinj (LocalizedModule.mk ell 1)
      (LocalizedModule.mk x 1) = algebraMap R Q
        (nativeCoextensionOriginalDualEquiv (R := R) (S := S) ell x) := by
  let j := nativeCoextensionFunctionalLocalizationMap (R := R) (S := S) (Q := Q)
  letI : IsLocalizedModule P j :=
    nativeCoextensionFunctionalLocalizationMap_isLocalizedModule (S := S) P hinj
  change functionalSourceLocalizationEquiv P
    ((IsLocalizedModule.iso P j) (LocalizedModule.mk ell 1))
      (LocalizedModule.mkLinearMap P S x) = _
  rw [functionalSourceLocalizationEquiv_apply_mk, IsLocalizedModule.iso_mk_one]
  rfl

end LinearStudy
