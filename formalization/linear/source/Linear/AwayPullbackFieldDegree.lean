module
public import Linear.AwayFractionEmbedding
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.FieldTheory.IntermediateField.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

theorem awayFractionEmbedding_isFractionRing
    {K B : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    (a : B) (ha : a ≠ 0) :
    letI : Algebra (Localization.Away a) (FractionRing B) :=
      (awayFractionEmbedding (K := K) a ha).toRingHom.toAlgebra
    IsFractionRing (Localization.Away a) (FractionRing B) := by
  let A := Localization.Away a
  let L := FractionRing B
  letI : Algebra A L := (awayFractionEmbedding (K := K) a ha).toRingHom.toAlgebra
  letI : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq
    (fun b => (awayFractionEmbedding_algebraMap (K := K) a ha b).symm)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers a) A L

/-- The actual pullback rank equals the degree of its actual image-field
extension. The target and source actions are specified separately, even
though the underlying coordinate domain is the same. -/
theorem awayPullback_finrank_eq_fieldRange
    {K B : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    (a : B) (ha : a ≠ 0) (γ : FractionRing B →ₐ[K] FractionRing B)
    (φ : B →ₐ[K] Localization.Away a)
    (h : (awayFractionEmbedding (K := K) a ha).comp φ =
      γ.comp (IsScalarTower.toAlgHom K B (FractionRing B))) :
    letI : Algebra B (Localization.Away a) := φ.toRingHom.toAlgebra
    letI : SMul B (Localization.Away a) := φ.toRingHom.toAlgebra.toSMul
    letI : Module B (Localization.Away a) := Algebra.toModule
    Module.finrank B (Localization.Away a) = Module.finrank γ.fieldRange (FractionRing B) := by
  let A := Localization.Away a
  let L := FractionRing B
  let E := γ.fieldRange
  let θ : B →+* E := γ.equivFieldRange.toRingHom.comp (algebraMap B L)
  letI : Algebra B E := θ.toAlgebra
  let ε : L ≃ₐ[B] E :=
    { γ.equivFieldRange.toRingEquiv with commutes' := fun b => rfl }
  letI : IsFractionRing B E := IsFractionRing.of_algEquiv ε
  let e := awayFractionEmbedding (K := K) a ha
  letI : Algebra A L := e.toRingHom.toAlgebra
  letI : IsFractionRing A L := awayFractionEmbedding_isFractionRing a ha
  letI : Algebra B A := φ.toRingHom.toAlgebra
  letI : SMul B A := φ.toRingHom.toAlgebra.toSMul
  letI : Module B A := Algebra.toModule
  letI : Algebra B L := (e.toRingHom.comp φ.toRingHom).toAlgebra
  letI : SMul B L := (e.toRingHom.comp φ.toRingHom).toAlgebra.toSMul
  letI : Module B L := Algebra.toModule
  letI : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower B E L := IsScalarTower.of_algebraMap_eq (fun b => by
    exact AlgHom.congr_fun h b)
  exact (IsFractionRing.finrank_eq B E A L).symm

end LinearStudy
