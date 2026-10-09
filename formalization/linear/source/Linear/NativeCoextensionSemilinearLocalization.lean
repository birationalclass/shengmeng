module
public import Linear.NativeCoextensionLocalizationUpper
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

/-- The canonical comparison from the ORIGINAL native upper-ring dual
to the ACTUAL localized native upper-ring dual, semilinear for the
original numerator ring homomorphism. -/
def finiteNativeCoextensionSemilinearLocalizationMap
    (hinj : Function.Injective (algebraMap R Q)) :
    let S' := LocalizedModule P S
    letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))
      →ₛₗ[LocalizedModule.numeratorRingHom (S := P) (A := S)]
        ((ModuleCat.coextendScalars (algebraMap Q S')).obj (ModuleCat.of Q Q)) := by
  let S' := LocalizedModule P S
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  let D := (ModuleCat.restrictScalars (algebraMap R S)).obj
    ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))
  let e := finiteNativeCoextensionLocalizedTargetEquiv (S := S) P hinj
  exact
    { toFun := fun ell => e (LocalizedModule.mk (ell : D) 1)
      map_add' := by
        intro ell psi
        change e ((LocalizedModule.mkLinearMap P D) (ell + psi)) =
          e ((LocalizedModule.mkLinearMap P D) ell) + e ((LocalizedModule.mkLinearMap P D) psi)
        rw [map_add, map_add]
      map_smul' := by
        intro b ell
        exact finiteNativeCoextensionLocalizedTargetEquiv_upper_smul_original P hinj ell b }

/-- Original values are preserved by the actual semilinear native map. -/
theorem finiteNativeCoextensionSemilinearLocalizationMap_apply_original
    (hinj : Function.Injective (algebraMap R Q)) :
    let S' := LocalizedModule P S
    letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    ∀ ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R), ∀ x : S,
      nativeCoextensionOriginalDualEquiv (R := Q) (S := S')
        (finiteNativeCoextensionSemilinearLocalizationMap P hinj ell) (LocalizedModule.mk x 1) =
          algebraMap R Q (nativeCoextensionOriginalDualEquiv (R := R) (S := S) ell x) := by
  let S' := LocalizedModule P S
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  dsimp only
  intro ell x
  exact finiteNativeCoextensionLocalizedTargetEquiv_apply_original P hinj ell x

end LinearStudy
