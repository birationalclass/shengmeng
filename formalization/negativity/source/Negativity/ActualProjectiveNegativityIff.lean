module

public import Negativity.ActualProjectiveNegativity
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: the full effectivity equivalence in the actual
projective negativity lemma (1), over any normal base, for real Cartier
divisors with negative relative nefness. Projectivity consists solely of
actual relative closed embeddings on affine opens. The difficult reverse
implication is the actual geometric theorem; the forward implication is
the actual scheme-cycle effectivity pushforward. -/
theorem actual_projective_negativity_effectivity_iff
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hproj : ActualLocallyProjective f)
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (d : τ → ℝ)
    (hnef : ActualRelativeNef k (f ≫ b) f A (fun t => -d t)) :
    (∀ x : X, 0 ≤ ∑ t, d t * ((A t).coefficient hnX x : ℝ)) ↔
      CycleEffective (AlgebraicCycle.map f Order.coheight Order.coheight
        (∑ t, (A t).weightedWeilCycle hnX (d t))) := by
  constructor
  · intro he
    apply scheme_cycle_map_effective f Order.coheight Order.coheight
    intro x
    simpa [CartierAtlas.weightedWeilCycle, CartierAtlas.weilCycle] using he x
  · intro hp
    exact actual_projective_negativity_part_one k b f hf hnX hnY hproj A d hp hnef

end
end Negativity
