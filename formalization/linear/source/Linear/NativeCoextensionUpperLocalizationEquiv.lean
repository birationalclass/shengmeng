module
public import Linear.NativeCoextensionUpperLocalizationProperty
public import Linear.NativeLocalizedUpperAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S Q : Type u} [CommRing R] [CommRing S] [CommRing Q]
variable [Algebra R S] [Algebra R Q] [Module.Finite R S]
variable (P : Submonoid R) [IsLocalization P Q]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The original ACTUAL native dual, localized over the original upper
ring, is the ACTUAL native coextension after localization. This is linear
over the localized upper ring, not just the localized normalization base. -/
def finiteNativeCoextensionUpperLocalizationEquiv
    (hinj : Function.Injective (algebraMap R Q)) :
    let S' := LocalizedModule P S
    letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    letI : Algebra S S' := nativeLocalizedUpperAlgebra P
    letI : IsLocalization (Algebra.algebraMapSubmonoid S P) S' :=
      nativeLocalizedUpperAlgebra_isLocalization P
    let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    letI : Module S' (LocalizedModule (Algebra.algebraMapSubmonoid S P) D) :=
      LocalizedModule.moduleOfIsLocalization
    LocalizedModule (Algebra.algebraMapSubmonoid S P) D ≃ₗ[S']
      ((ModuleCat.coextendScalars (algebraMap Q S')).obj (ModuleCat.of Q Q)) := by
  let S' := LocalizedModule P S
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  letI : Algebra S S' := nativeLocalizedUpperAlgebra P
  letI : IsLocalization (Algebra.algebraMapSubmonoid S P) S' :=
    nativeLocalizedUpperAlgebra_isLocalization P
  let N := (ModuleCat.coextendScalars (algebraMap Q S')).obj (ModuleCat.of Q Q)
  let Y := (ModuleCat.restrictScalars (LocalizedModule.numeratorRingHom (S := P) (A := S))).obj N
  letI : IsScalarTower S S' Y := IsScalarTower.of_compHom S S' Y
  let j := finiteNativeCoextensionUpperLocalizationMap (S := S) P hinj
  letI : IsLocalizedModule (Algebra.algebraMapSubmonoid S P) j :=
    finiteNativeCoextensionUpperLocalizationMap_isLocalizedModule P hinj
  exact (IsLocalizedModule.iso (Algebra.algebraMapSubmonoid S P) j).extendScalarsOfIsLocalization
    (Algebra.algebraMapSubmonoid S P) S'

/-- The upper-ring linear comparison retains every original functional
value under the actual base localization. -/
theorem finiteNativeCoextensionUpperLocalizationEquiv_apply_original
    (hinj : Function.Injective (algebraMap R Q)) :
    let S' := LocalizedModule P S
    letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    letI : Algebra S S' := nativeLocalizedUpperAlgebra P
    letI : IsLocalization (Algebra.algebraMapSubmonoid S P) S' :=
      nativeLocalizedUpperAlgebra_isLocalization P
    ∀ ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R), ∀ x : S,
      nativeCoextensionOriginalDualEquiv (R := Q) (S := S')
        (finiteNativeCoextensionUpperLocalizationEquiv P hinj
          (LocalizedModule.mk ell 1)) (LocalizedModule.mk x 1) =
        algebraMap R Q (nativeCoextensionOriginalDualEquiv (R := R) (S := S) ell x) := by
  let S' := LocalizedModule P S
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  letI : Algebra S S' := nativeLocalizedUpperAlgebra P
  letI : IsLocalization (Algebra.algebraMapSubmonoid S P) S' :=
    nativeLocalizedUpperAlgebra_isLocalization P
  let N := (ModuleCat.coextendScalars (algebraMap Q S')).obj (ModuleCat.of Q Q)
  let Y := (ModuleCat.restrictScalars (LocalizedModule.numeratorRingHom (S := P) (A := S))).obj N
  letI : IsScalarTower S S' Y := IsScalarTower.of_compHom S S' Y
  let j := finiteNativeCoextensionUpperLocalizationMap (S := S) P hinj
  letI : IsLocalizedModule (Algebra.algebraMapSubmonoid S P) j :=
    finiteNativeCoextensionUpperLocalizationMap_isLocalizedModule P hinj
  dsimp only
  intro ell x
  change nativeCoextensionOriginalDualEquiv (R := Q) (S := S')
      ((IsLocalizedModule.iso (Algebra.algebraMapSubmonoid S P) j)
        (LocalizedModule.mk ell 1)) (LocalizedModule.mk x 1) = _
  rw [IsLocalizedModule.iso_mk_one]
  exact finiteNativeCoextensionSemilinearLocalizationMap_apply_original P hinj ell x

end LinearStudy
