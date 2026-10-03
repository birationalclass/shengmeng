module

public import Negativity.ActualOpenPushforward
public import Negativity.BirationalComposition
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actual_cycle_push_at_codimension_one_preimage
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (D : AlgebraicCycle X ℝ) (x : X) (hx : Order.coheight (f x) = 1) :
    AlgebraicCycle.map f Order.coheight Order.coheight D (f x) = D x := by
  rw [scheme_cycle_strictTransform_coefficient hnY f hf D ⟨f x, hx⟩]
  congr 1
  have := hnY (f x)
  obtain ⟨z, hz, _, _, hu⟩ := proper_birational_codimensionOne_unique_preimage f hf (f x) hx
  exact (hu _ (geometricStrictTransform_image hnY f hf ⟨f x, hx⟩)).trans (hu x rfl).symm

/-- Final theorem: actual Weil-cycle pushforward composes through two
actual proper birational maps to normal schemes. The intermediate
codimension-one property is proved from actual unique stalk-isomorphic
preimages, so no cycle composition or multiplicity input is supplied. -/
theorem actual_proper_birational_weil_pushforward_comp
    {Z X Y : Scheme.{u}} [IsIntegral Z] [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (p : Z ⟶ X) [IsProper p] (hp : BirationalMorphism p)
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (D : AlgebraicCycle Z ℝ) (hD : AlgebraicCycle.IsWeilDivisor D) :
    AlgebraicCycle.map (p ≫ f) Order.coheight Order.coheight D =
      AlgebraicCycle.map f Order.coheight Order.coheight
        (AlgebraicCycle.map p Order.coheight Order.coheight D) := by
  apply proper_birational_weil_cycle_pushforward hnY (p ≫ f)
    (actual_birational_morphism_comp p f hp hf) _ _
    (actual_weil_cycle_pushforward_isWeil f _ (actual_weil_cycle_pushforward_isWeil p D hD)) hD
  intro z hz
  have hz' : Order.coheight (f (p z)) = 1 := by simpa only [Scheme.Hom.comp_apply] using hz
  have := hnY (f (p z))
  obtain ⟨x, _, _, hc, hu⟩ := proper_birational_codimensionOne_unique_preimage f hf (f (p z)) hz'
  have hpx : Order.coheight (p z) = 1 := (hu (p z) rfl) ▸ hc
  simp only [Scheme.Hom.comp_apply]
  rw [actual_cycle_push_at_codimension_one_preimage hnY f hf _ (p z) hz',
    actual_cycle_push_at_codimension_one_preimage hnX p hp D z hpx]

end
end Negativity
