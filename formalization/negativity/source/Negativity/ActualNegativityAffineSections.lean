module

public import Negativity.ActualNegativityConstruction
public import Negativity.CartierAffineSections
public import Negativity.CartierInverse
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: actual negativity with geometric affine section-cover
data over an affine normal base. No anti-positive degree condition, no E
effectivity, no exceptional coverage and no curve-existence hypothesis are
supplied. Actual positive degree follows from affine nonvanishing loci,
then the negative Cartier divisor is effectively twisted and used in the
proved maximum-ratio contradiction. The remaining projective bridge is
construction of the actual Cartier section-cover data from O(1). -/
theorem actual_negativity_of_affine_section_cover
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [CompactSpace X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {ι τ σ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (d : τ → ℝ)
    (hpush : CycleEffective (AlgebraicCycle.map f Order.coheight Order.coheight
      (∑ t, (A t).weightedWeilCycle hnX (d t))))
    (hnef : ActualRelativeNef k (f ≫ b) f A (fun t => -d t))
    (A₀ : CartierAtlas X ι) (S : CartierAffineSectionCover A₀ σ) :
    ∀ x : X, 0 ≤ ∑ t, d t * ((A t).coefficient hnX x : ℝ) := by
  apply actual_negativity_of_strictly_negative_cartier k b f hf hnX hnY A d
    hpush hnef A₀.inverse
  intro C _ hd j _ hj _hc
  have := hj
  rw [complete_integral_curve_cartier_intersection_inverse hnX hd k (j ≫ f ≫ b) j A₀]
  exact neg_neg_of_pos (complete_integral_curve_positive_of_affine_section_cover
    hd k (j ≫ f ≫ b) j A₀ S)

end
end Negativity
