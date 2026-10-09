module
public import Linear.NativeCoextensionLocalizedTarget
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S Q : Type u} [CommRing R] [CommRing S] [CommRing Q]
variable [Algebra R S] [Algebra R Q] [Module.Finite R S]
variable (P : Submonoid R) [IsLocalization P Q]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

omit [Module.Finite R S] in
/-- The actual upper-ring action is precomposition by multiplication,
after BOTH original scalar comparisons. -/
theorem nativeCoextensionOriginalDualEquiv_upper_smul
    (ell : (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)))
    (b x : S) :
    nativeCoextensionOriginalDualEquiv (R := R) (S := S) (b • ell) x =
      nativeCoextensionOriginalDualEquiv (R := R) (S := S) ell (x * b) := by
  rfl

/-- Localizing the original native dual preserves its actual upper-ring
multiplication action; no freeness or Cohen--Macaulay hypothesis is used. -/
theorem finiteNativeCoextensionLocalizationEquiv_upper_smul_original
    (hinj : Function.Injective (algebraMap R Q)) :
    let S' := LocalizedModule P S
    letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    ∀ ell : (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)), ∀ b : S,
      finiteNativeCoextensionLocalizationEquiv P hinj (LocalizedModule.mk (b • ell) 1) =
        (finiteNativeCoextensionLocalizationEquiv P hinj (LocalizedModule.mk ell 1)).comp
          (LinearMap.mulRight Q (LocalizedModule.mk b 1 : S')) := by
  let S' := LocalizedModule P S
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  dsimp only
  intro ell b
  apply (functionalSourceLocalizationRestriction_bijective (Q := Q) (M := S) P).1
  ext x
  change finiteNativeCoextensionLocalizationEquiv P hinj
      (LocalizedModule.mk (b • ell) 1) (LocalizedModule.mk x 1) =
    finiteNativeCoextensionLocalizationEquiv P hinj (LocalizedModule.mk ell 1)
      (LocalizedModule.mk x 1 * LocalizedModule.mk b 1)
  rw [LocalizedModule.mk_mul_mk, one_mul]
  rw [finiteNativeCoextensionLocalizationEquiv_apply_mk,
    finiteNativeCoextensionLocalizationEquiv_apply_mk,
    nativeCoextensionOriginalDualEquiv_upper_smul]

/-- The comparison with mathlib's ACTUAL localized native coextension
preserves every original upper-ring scalar. -/
theorem finiteNativeCoextensionLocalizedTargetEquiv_upper_smul_original
    (hinj : Function.Injective (algebraMap R Q)) :
    let S' := LocalizedModule P S
    letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    ∀ ell : (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)), ∀ b : S,
      finiteNativeCoextensionLocalizedTargetEquiv P hinj (LocalizedModule.mk (b • ell) 1) =
        (LocalizedModule.mk b 1 : S') •
          finiteNativeCoextensionLocalizedTargetEquiv P hinj (LocalizedModule.mk ell 1) := by
  let S' := LocalizedModule P S
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  dsimp only
  intro ell b
  apply (nativeCoextensionOriginalDualEquiv (R := Q) (S := S')).injective
  apply (functionalSourceLocalizationRestriction_bijective (Q := Q) (M := S) P).1
  ext x
  change nativeCoextensionOriginalDualEquiv (R := Q) (S := S')
      (finiteNativeCoextensionLocalizedTargetEquiv P hinj
        (LocalizedModule.mk (b • ell) 1)) (LocalizedModule.mk x 1) =
    nativeCoextensionOriginalDualEquiv (R := Q) (S := S')
      ((LocalizedModule.mk b 1 : S') •
        finiteNativeCoextensionLocalizedTargetEquiv P hinj (LocalizedModule.mk ell 1))
      (LocalizedModule.mk x 1)
  rw [nativeCoextensionOriginalDualEquiv_upper_smul,
    LocalizedModule.mk_mul_mk, one_mul]
  rw [finiteNativeCoextensionLocalizedTargetEquiv_apply_original,
    finiteNativeCoextensionLocalizedTargetEquiv_apply_original,
    nativeCoextensionOriginalDualEquiv_upper_smul]

end LinearStudy
