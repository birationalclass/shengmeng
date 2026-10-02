module

public import Negativity.CartierPushPull
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

/-- Actual cycle pushforward preserves every coefficient over a target
open on which the morphism is an isomorphism. Both its unique preimage
and multiplicity one are derived from that actual isomorphism. -/
theorem actual_cycle_coefficient_over_isomorphism_open
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.Opens) [IsIso (f ∣_ U)] (x : X) (hx : f x ∈ U)
    (D : AlgebraicCycle X ℝ) :
    AlgebraicCycle.map f Order.coheight Order.coheight D (f x) = D x := by
  classical
  let z : (f ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  have hweight : Order.coheight x = Order.coheight (f x) := by
    calc
      Order.coheight x = Order.coheight z :=
        coheight_eq_of_isOpenImmersion (x := z) (f := (f ⁻¹ᵁ U).ι)
      _ = Order.coheight ((f ∣_ U) z) :=
        (coheight_eq_of_isOpenImmersion (x := z) (f := f ∣_ U)).symm
      _ = Order.coheight (U.ι ((f ∣_ U) z)) :=
        (coheight_eq_of_isOpenImmersion (x := (f ∣_ U) z) (f := U.ι)).symm
      _ = Order.coheight (f x) :=
        by simpa only [Scheme.Opens.ι_apply] using
          congrArg (fun y : Y => Order.coheight y) (morphismRestrict_base_coe f U z)
  have hunique : ∀ w : X, f w = f x → w = x := by
    intro w hw
    have hwU : f w ∈ U := hw ▸ hx
    have he : (f ∣_ U) ⟨w, hwU⟩ = (f ∣_ U) z := by
      apply Subtype.ext
      rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
      exact hw
    exact congrArg Subtype.val ((f ∣_ U).isOpenEmbedding.injective he)
  have : IsIso (f.stalkMap x) := stalkMap_isIso_over_isomorphism_open f U x hx
  change (∑ᶠ w ∈ f.base ⁻¹' {f x}, D w *
    (AlgebraicCycle.mapCoeff f Order.coheight Order.coheight w : ℝ)) = D x
  have hsingle : ∀ w : X, w ≠ x →
      (∑ᶠ (_ : w ∈ f.base ⁻¹' {f x}), D w *
        (AlgebraicCycle.mapCoeff f Order.coheight Order.coheight w : ℝ)) = 0 := by
    intro w hw
    have hne : f w ≠ f x := fun he => hw (hunique w he)
    simp [Set.mem_preimage, Set.mem_singleton_iff, hne]
  rw [finsum_eq_single _ x hsingle,
    scheme_mapCoeff_of_same_weight f Order.coheight Order.coheight x hweight,
    scheme_residueDegree_of_stalk_iso]
  simp

/-- Final theorem: if the actual pushforward cycle is effective, every
negative actual coefficient lies over the actual center. No numerical
strict-transform model or exceptional-prime identification is assumed. -/
theorem actual_negative_coefficient_image_in_center
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (D : AlgebraicCycle X ℝ)
    (he : CycleEffective (AlgebraicCycle.map f Order.coheight Order.coheight D))
    (x : X) (hneg : D x < 0) :
    ∀ U : Y.Opens, f x ∈ U → ¬ IsIso (f ∣_ U) := by
  intro U hx hIso
  have : IsIso (f ∣_ U) := hIso
  have hc := he (f x)
  rw [actual_cycle_coefficient_over_isomorphism_open f U x hx D] at hc
  exact (not_lt_of_ge hc) hneg

end
end Negativity
