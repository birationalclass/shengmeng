module

public import Negativity.InfinitesimalIdempotents
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Actual quotient-ring identification of functions on an affine power
thickening. Both rings and the comparison come from the actual scheme. -/
def actualAffineThickeningSectionsEquiv (X : Scheme.{u}) [IsAffine X]
    (I : X.IdealSheafData) (n : ℕ) :
    Γ(actualPowerThickening I n, ⊤) ≃+*
      Γ(X, ⊤) ⧸ (I.ideal ⟨⊤, isAffineOpen_top X⟩) ^ (n + 1) := by
  simpa! only [actualPowerThickening, Hom.preimage_top, IdealSheafData.ideal_pow,
    Pi.pow_apply] using
    ((I ^ (n + 1)).subschemeObjIso ⟨⊤, isAffineOpen_top X⟩).commRingCatIsoToRingEquiv

theorem actual_affine_thickening_sections_pullback (X : Scheme.{u}) [IsAffine X]
    (I : X.IdealSheafData) (n : ℕ) (r : Γ(X, ⊤)) :
    actualAffineThickeningSectionsEquiv X I n ((I ^ (n + 1)).subschemeι.appTop r) =
      Ideal.Quotient.mk ((I.ideal ⟨⊤, isAffineOpen_top X⟩) ^ (n + 1)) r := by
  have h := congrArg (fun f => f r)
    ((I ^ (n + 1)).subschemeι_app ⟨⊤, isAffineOpen_top X⟩)
  apply (actualAffineThickeningSectionsEquiv X I n).symm.injective
  simpa! [actualAffineThickeningSectionsEquiv, actualPowerThickening,
    Iso.commRingCatIsoToRingEquiv, RingEquiv.ofRingHom] using h

/-- Final theorem: the actual restriction of regular functions between
affine infinitesimal thickenings is the quotient transition map. The
comparison is derived from genuine scheme inclusions and the actual
structure-sheaf quotient isomorphisms; it is not a compatibility input. -/
theorem actual_affine_thickening_sections_transition (X : Scheme.{u}) [IsAffine X]
    (I : X.IdealSheafData) {m n : ℕ} (h : m ≤ n)
    (s : Γ(actualPowerThickening I n, ⊤)) :
    actualAffineThickeningSectionsEquiv X I m
        ((actualPowerThickeningInclusion I h).appTop s) =
      Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := I.ideal ⟨⊤, isAffineOpen_top X⟩)
          (Nat.add_le_add_right h 1)) (actualAffineThickeningSectionsEquiv X I n s) := by
  obtain ⟨r, rfl⟩ := (I ^ (n + 1)).subschemeι_app_surjective
    ⟨⊤, isAffineOpen_top X⟩ s
  have hf := IdealSheafData.inclusion_subschemeι
    (show I ^ (n + 1) ≤ I ^ (m + 1) from by
      intro U
      simpa only [IdealSheafData.ideal_pow, Pi.pow_apply] using
        (Ideal.pow_le_pow_right (I := I.ideal U) (Nat.add_le_add_right h 1)))
  have hr := congrArg (fun f : actualPowerThickening I m ⟶ X => f.appTop r) hf
  change (actualPowerThickeningInclusion I h).appTop
    ((I ^ (n + 1)).subschemeι.appTop r) =
      (I ^ (m + 1)).subschemeι.appTop r at hr
  change actualAffineThickeningSectionsEquiv X I m
      ((actualPowerThickeningInclusion I h).appTop ((I ^ (n + 1)).subschemeι.appTop r)) =
    Ideal.Quotient.factor _ (actualAffineThickeningSectionsEquiv X I n
      ((I ^ (n + 1)).subschemeι.appTop r))
  erw [hr, actual_affine_thickening_sections_pullback,
    actual_affine_thickening_sections_pullback]
  rfl

end
end Negativity
