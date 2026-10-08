module
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.FieldTheory.IntermediateField.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Generic rank of a real domain map equals the degree of its actual
image field. Source and target instances are captured separately. -/
theorem fractionPullback_finrank_eq_fieldRange
    {k R S K L : Type*} [Field k] [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Field K] [Field L]
    [Algebra k R] [Algebra k S] [Algebra R K] [Algebra S L]
    [Algebra k K] [Algebra k L] [IsScalarTower k R K] [IsScalarTower k S L]
    [IsFractionRing R K] [IsFractionRing S L]
    (γ : K →ₐ[k] L) (φ : R →ₐ[k] S)
    (h : (IsScalarTower.toAlgHom k S L).comp φ =
      γ.comp (IsScalarTower.toAlgHom k R K)) :
    letI : Algebra R S := φ.toRingHom.toAlgebra
    letI : SMul R S := φ.toRingHom.toAlgebra.toSMul
    letI : Module R S := Algebra.toModule
    Module.finrank R S = Module.finrank γ.fieldRange L := by
  let E := γ.fieldRange
  let θ : R →+* E := γ.equivFieldRange.toRingHom.comp (algebraMap R K)
  letI : Algebra R E := θ.toAlgebra
  let ε : K ≃ₐ[R] E :=
    { γ.equivFieldRange.toRingEquiv with commutes' := fun r => rfl }
  letI : IsFractionRing R E := IsFractionRing.of_algEquiv ε
  let ι := IsScalarTower.toAlgHom k S L
  letI : Algebra R S := φ.toRingHom.toAlgebra
  letI : SMul R S := φ.toRingHom.toAlgebra.toSMul
  letI : Module R S := Algebra.toModule
  letI : Algebra R L := (ι.toRingHom.comp φ.toRingHom).toAlgebra
  letI : SMul R L := (ι.toRingHom.comp φ.toRingHom).toAlgebra.toSMul
  letI : Module R L := Algebra.toModule
  letI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R E L := IsScalarTower.of_algebraMap_eq (fun r => by
    exact AlgHom.congr_fun h r)
  exact (IsFractionRing.finrank_eq R E S L).symm

end LinearStudy
