module
public import Linear.NativeIntegerPrimeTwist
import all Mathlib.RingTheory.OreLocalization.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (a : S) (ha : a ∈ 𝓑 1)
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- Actual coordinate multiplication sends structure-ring sections to
locally homogeneous fractions of the requested integer degree. -/
def nativeIntegerTwistSectionMap (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U →ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) k U where
  toFun r := ⟨fun p => nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hp p) k
    (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (r.1 p)), by
      apply (Submodule.mem_carrier _).1
      dsimp only [nativeProjectiveModuleSections, Set.mem_ofPred_eq]
      simpa only [zero_add] using nativeIntegerTwistLocalFraction_forward 𝓑 a ha k 0 hp
        (nativeStructureLocalFraction_moduleLocalFraction 𝓑 r.property)⟩
  map_add' r s := by
    apply Subtype.ext
    funext p
    change nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hp p) k
      (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (r.1 p + s.1 p)) = _
    rw [(nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1).map_add]
    exact (nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hp p) k).map_add _ _
  map_smul' r s := by
    apply Subtype.ext
    funext p
    change nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hp p) k
        (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 ((r.1 p) • (s.1 p))) = _
    rw [(nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1).map_smul]
    exact (nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hp p) k).map_smul _ _

/-- The opposite coordinate power sends the original degree-k sections
to original degree-zero sections. -/
def nativeIntegerTwistSectionToZero (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal) :
    nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) k U →ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) 0 U where
  toFun f := ⟨fun p => nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hp p) (-k) (f.1 p), by
      apply (Submodule.mem_carrier _).1
      dsimp only [nativeProjectiveModuleSections, Set.mem_ofPred_eq]
      simpa only [add_neg_cancel] using
        nativeIntegerTwistLocalFraction_forward 𝓑 a ha (-k) k hp f.property⟩
  map_add' f g := by
    apply Subtype.ext
    funext p
    exact (nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hp p) (-k)).map_add _ _
  map_smul' r f := by
    apply Subtype.ext
    funext p
    exact (nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hp p) (-k)).map_smul (r.1 p) (f.1 p)

/-- The actual structure ring trivializes every integer twist on every
original open where the degree-one coordinate is nonvanishing. Both maps
are explicitly given on the original localized module values. -/
def nativeIntegerTwistSectionFrame (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U ≃ₗ[
      (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) k U where
  toFun := nativeIntegerTwistSectionMap 𝓑 a ha k U hp
  invFun f := (nativeStructureRingZeroModuleSectionEquiv 𝓑 U).symm
    (nativeIntegerTwistSectionToZero 𝓑 a ha k U hp f)
  left_inv r := by
    apply (nativeStructureRingZeroModuleSectionEquiv 𝓑 U).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    funext p
    exact nativePrimeIntegerTwistEquiv_neg_apply 𝓑 p.1 a (hp p) k
      (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (r.1 p))
  right_inv f := by
    apply Subtype.ext
    funext p
    have h := congrArg (fun z => z.1 p)
      ((nativeStructureRingZeroModuleSectionEquiv 𝓑 U).apply_symm_apply
        (nativeIntegerTwistSectionToZero 𝓑 a ha k U hp f))
    change nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1
        (((nativeStructureRingZeroModuleSectionEquiv 𝓑 U).symm
          (nativeIntegerTwistSectionToZero 𝓑 a ha k U hp f)).1 p) =
      nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hp p) (-k) (f.1 p) at h
    change nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hp p) k
      (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1
        (((nativeStructureRingZeroModuleSectionEquiv 𝓑 U).symm
          (nativeIntegerTwistSectionToZero 𝓑 a ha k U hp f)).1 p)) = f.1 p
    rw [h]
    simpa only [neg_neg] using
      nativePrimeIntegerTwistEquiv_neg_apply 𝓑 p.1 a (hp p) (-k) (f.1 p)
  map_add' := (nativeIntegerTwistSectionMap 𝓑 a ha k U hp).map_add
  map_smul' := (nativeIntegerTwistSectionMap 𝓑 a ha k U hp).map_smul

/-- Every actual open restriction commutes with these integer-power
frames on one coordinate chart. No integer-index data cast is required. -/
theorem nativeIntegerTwistSectionFrame_restrict (k : ℤ)
    {U V : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ} (i : U ⟶ V)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U) :
    (nativeProjectiveModulePresheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) k).map i
        (nativeIntegerTwistSectionFrame 𝓑 a ha k U hp r) =
      nativeIntegerTwistSectionFrame 𝓑 a ha k V (fun p => hp (i.unop p))
        ((ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.map i r) := by
  apply Subtype.ext
  funext p
  rfl

/-- Its actual value is coordinate-to-the-k times the structure-ring
value in the original ring localization. -/
theorem nativeIntegerTwistSectionFrame_localizedValue (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U) (p : U.unop) :
    nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1
      ((nativeIntegerTwistSectionFrame 𝓑 a ha k U hp r).1 p) =
      ((nativePrimeCoordinateUnit 𝓑 p.1 a (hp p) ^ k :
        (Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl)ˣ) :
          Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) * (r.1 p).val := by
  rw [show (nativeIntegerTwistSectionFrame 𝓑 a ha k U hp r).1 p =
    nativePrimeIntegerTwistEquiv 𝓑 p.1 a (hp p) k
      (nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (r.1 p)) from rfl]
  rw [nativePrimeIntegerTwistEquiv_localizedValue]
  change _ * ((nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1)
    ((nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1).symm (r.1 p).val)) = _
  rw [LinearEquiv.apply_symm_apply]

end LinearStudy
