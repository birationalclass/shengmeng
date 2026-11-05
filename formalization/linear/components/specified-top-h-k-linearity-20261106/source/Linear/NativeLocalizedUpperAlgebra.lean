module
public import Mathlib.RingTheory.Localization.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Submonoid R)

/-- The actual original upper ring acts on its localized carrier through
the actual numerator ring homomorphism. -/
@[instance_reducible] def nativeLocalizedUpperAlgebra : Algebra S (LocalizedModule P S) :=
  (LocalizedModule.numeratorRingHom (S := P) (A := S)).toAlgebra

/-- The original base-module localization is the actual upper-ring
localization at the image multiplicative set. -/
theorem nativeLocalizedUpperAlgebra_isLocalization :
    letI := nativeLocalizedUpperAlgebra (S := S) P
    IsLocalization (Algebra.algebraMapSubmonoid S P) (LocalizedModule P S) := by
  letI := nativeLocalizedUpperAlgebra (S := S) P
  letI : IsScalarTower R S (LocalizedModule P S) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmap : (IsScalarTower.toAlgHom R S (LocalizedModule P S)).toLinearMap =
      LocalizedModule.mkLinearMap P S := by
    ext x
    rfl
  apply (isLocalizedModule_iff_isLocalization (S := P) (A := S)
    (Aₛ := LocalizedModule P S)).mp
  rw [hmap]
  infer_instance

end LinearStudy
