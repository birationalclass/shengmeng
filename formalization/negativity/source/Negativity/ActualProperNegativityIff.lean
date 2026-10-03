module

public import Negativity.ActualProperNegativity
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: the full effectivity equivalence for actual proper
real-Cartier negativity (1), with an arbitrary normal base variety and
an algebraically closed field of arbitrary characteristic. The reverse
implication uses the constructed Hartshorne normal modification and
actual Cartier sections; the forward implication uses actual effective
cycle pushforward. No projectivity or auxiliary proof input remains. -/
theorem actual_proper_negativity_effectivity_iff
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
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
    exact actual_proper_negativity_part_one k b f hf hnX hnY A d hp hnef

end
end Negativity
