module
public import Linear.NativeIntegerPrimeTwist
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The actual fraction a/b is a structure-ring section wherever b is
nonvanishing; its uniform homogeneous fraction has degree zero. -/
def nativeCoordinateRatioSection (a : S) (ha : a ∈ 𝓑 1)
    (b : S) (hb : b ∈ 𝓑 1) (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hpb : ∀ p : U.unop, b ∉ p.1.asHomogeneousIdeal) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U :=
  ⟨fun p => HomogeneousLocalization.mk ⟨1, ⟨a, ha⟩, ⟨b, hb⟩, hpb p⟩, by
    intro p
    exact ⟨U.unop, p.2, 𝟙 U.unop, 1, ⟨a, ha⟩, ⟨b, hb⟩, hpb, fun _ => rfl⟩⟩

/-- Its pointwise value is the actual localized fraction a/b. -/
theorem nativeCoordinateRatioSection_localizedValue (a : S) (ha : a ∈ 𝓑 1)
    (b : S) (hb : b ∈ 𝓑 1) (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hpa : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (hpb : ∀ p : U.unop, b ∉ p.1.asHomogeneousIdeal) (p : U.unop) :
    ((nativeCoordinateRatioSection 𝓑 a ha b hb U hpb).1 p).val =
      ((nativePrimeCoordinateUnit 𝓑 p.1 a (hpa p) *
        (nativePrimeCoordinateUnit 𝓑 p.1 b (hpb p))⁻¹ :
          (Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl)ˣ) :
            Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) := by
  change (HomogeneousLocalization.mk ⟨1, ⟨a, ha⟩, ⟨b, hb⟩, hpb p⟩ :
    HomogeneousLocalization.AtPrime 𝓑 p.1.asHomogeneousIdeal.toIdeal).val = _
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk']
  symm
  apply (IsLocalization.eq_mk'_iff_mul_eq).2
  have hua : (nativePrimeCoordinateUnit 𝓑 p.1 a (hpa p) :
      Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) = algebraMap _ _ a :=
    IsUnit.unit_spec _
  have hub : (nativePrimeCoordinateUnit 𝓑 p.1 b (hpb p) :
      Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) = algebraMap _ _ b :=
    IsUnit.unit_spec _
  rw [← hub, ← hua, ← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]

/-- Reciprocal actual homogeneous fractions multiply to the unit
section on the original open, proved in the original localizations. -/
theorem nativeCoordinateRatioSection_mul_reciprocal (a : S) (ha : a ∈ 𝓑 1)
    (b : S) (hb : b ∈ 𝓑 1) (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hpa : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (hpb : ∀ p : U.unop, b ∉ p.1.asHomogeneousIdeal) :
    nativeCoordinateRatioSection 𝓑 a ha b hb U hpb *
      nativeCoordinateRatioSection 𝓑 b hb a ha U hpa = 1 := by
  apply Subtype.ext
  funext p
  apply HomogeneousLocalization.val_injective
  change ((HomogeneousLocalization.mk ⟨1, ⟨a, ha⟩, ⟨b, hb⟩, hpb p⟩ :
      HomogeneousLocalization.AtPrime 𝓑 p.1.asHomogeneousIdeal.toIdeal) *
    HomogeneousLocalization.mk ⟨1, ⟨b, hb⟩, ⟨a, ha⟩, hpa p⟩).val =
      (1 : HomogeneousLocalization.AtPrime 𝓑 p.1.asHomogeneousIdeal.toIdeal).val
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk']
  exact IsLocalization.mk'_mul_mk'_eq_one ⟨a, hpa p⟩ ⟨b, hpb p⟩

/-- The actual ratio a/b is a unit on an open where both coordinates
are nonvanishing, with the actual reciprocal b/a as inverse. -/
def nativeCoordinateRatioUnit (a : S) (ha : a ∈ 𝓑 1)
    (b : S) (hb : b ∈ 𝓑 1) (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hpa : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (hpb : ∀ p : U.unop, b ∉ p.1.asHomogeneousIdeal) :
    ((ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U)ˣ where
  val := nativeCoordinateRatioSection 𝓑 a ha b hb U hpb
  inv := nativeCoordinateRatioSection 𝓑 b hb a ha U hpa
  val_inv := nativeCoordinateRatioSection_mul_reciprocal 𝓑 a ha b hb U hpa hpb
  inv_val := nativeCoordinateRatioSection_mul_reciprocal 𝓑 b hb a ha U hpb hpa

/-- Actual structure sections evaluate in the original ring localization. -/
def nativeStructureSectionPointRingHom
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) (p : U.unop) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U →+*
      Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl where
  toFun r := (r.1 p).val
  map_one' := HomogeneousLocalization.val_one
  map_zero' := HomogeneousLocalization.val_zero
  map_add' _ _ := HomogeneousLocalization.val_add _ _
  map_mul' _ _ := HomogeneousLocalization.val_mul _ _

/-- Mapping the actual ratio unit to a point gives the quotient of
the two actual localized coordinate units. -/
theorem nativeCoordinateRatioUnit_pointMap (a : S) (ha : a ∈ 𝓑 1)
    (b : S) (hb : b ∈ 𝓑 1) (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hpa : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (hpb : ∀ p : U.unop, b ∉ p.1.asHomogeneousIdeal) (p : U.unop) :
    Units.map (nativeStructureSectionPointRingHom 𝓑 U p).toMonoidHom
      (nativeCoordinateRatioUnit 𝓑 a ha b hb U hpa hpb) =
      nativePrimeCoordinateUnit 𝓑 p.1 a (hpa p) *
        (nativePrimeCoordinateUnit 𝓑 p.1 b (hpb p))⁻¹ := by
  apply Units.ext
  exact nativeCoordinateRatioSection_localizedValue 𝓑 a ha b hb U hpa hpb p

/-- Every integer power of the actual ratio section has the expected
actual localized quotient-unit power. -/
theorem nativeCoordinateRatioUnit_zpow_pointValue (a : S) (ha : a ∈ 𝓑 1)
    (b : S) (hb : b ∈ 𝓑 1) (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hpa : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (hpb : ∀ p : U.unop, b ∉ p.1.asHomogeneousIdeal) (p : U.unop) (k : ℤ) :
    nativeStructureSectionPointRingHom 𝓑 U p
      (((nativeCoordinateRatioUnit 𝓑 a ha b hb U hpa hpb)^k :
        ((ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U)ˣ) :
          (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U) =
      (((nativePrimeCoordinateUnit 𝓑 p.1 a (hpa p) *
        (nativePrimeCoordinateUnit 𝓑 p.1 b (hpb p))⁻¹)^k :
          (Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl)ˣ) :
            Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) := by
  rw [← nativeCoordinateRatioUnit_pointMap 𝓑 a ha b hb U hpa hpb p,
    ← (Units.map (nativeStructureSectionPointRingHom 𝓑 U p).toMonoidHom).map_zpow]
  rfl

end LinearStudy
