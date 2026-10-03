module
public import Negativity.ActualProperNegativityIff
public import Negativity.ActualProperSupportDichotomy
public import Negativity.ActualProperClosedFiberConnected

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: both conclusions of actual proper real-Cartier
negativity over an algebraically closed field of arbitrary characteristic.
All curves, divisor operations, intersection signs, Chow modification and
closed-fiber connectedness are proved for the actual geometric objects.
No additional formal-functions or geometric-interface premise is supplied. -/
theorem actual_proper_negativity_lemma
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X] [IsNoetherian Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (d : τ → ℝ)
    (hnef : ActualRelativeNef k (f ≫ b) f A (fun t => -d t)) :
    ((∀ x : X, 0 ≤ ∑ t, d t * ((A t).coefficient hnX x : ℝ)) ↔
      CycleEffective (AlgebraicCycle.map f Order.coheight Order.coheight
        (∑ t, (A t).weightedWeilCycle hnX (d t)))) ∧
    ((∀ x : X, 0 ≤ ∑ t, d t * ((A t).coefficient hnX x : ℝ)) →
      ∀ y : Y,
        (∀ x : X, f x = y →
          x ∉ closure (∑ t, (A t).weightedWeilCycle hnX (d t)).support) ∨
        (∀ x : X, f x = y →
          x ∈ closure (∑ t, (A t).weightedWeilCycle hnX (d t)).support)) := by
  refine ⟨actual_proper_negativity_effectivity_iff k b f hf hnX hnY A d hnef, ?_⟩
  intro he
  exact actual_proper_support_dichotomy_of_connected_closed_fibers hnX k b f A d he hnef
    (actual_proper_birational_closed_fibers_connected f hf hnY)

#print axioms actual_proper_negativity_lemma
end
end Negativity
