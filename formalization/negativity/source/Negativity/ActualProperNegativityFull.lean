module

public import Negativity.ActualProperNegativityIff
public import Negativity.ActualProperSupportDichotomy
public import Negativity.GlobalClosedFiberConnectedness
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem, explicitly conditional: both conclusions of actual
proper real-Cartier negativity are connected to the single precise
remaining formal-functions comparison. Conclusion (1) itself has no
formal-functions hypothesis; only closed-fiber connectedness and thus
conclusion (2) use it. No supplied curves, intersections, modification,
normalization, support identities or other geometric inputs remain. -/
theorem actual_proper_negativity_of_actual_formal_functions
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X] [IsNoetherian Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (d : τ → ℝ)
    (hnef : ActualRelativeNef k (f ≫ b) f A (fun t => -d t))
    (hff : ActualClosedFiberFormalFunctions f) :
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
  have : Surjective f := proper_birational_surjective f hf
  exact actual_proper_support_dichotomy_of_connected_closed_fibers hnX k b f A d he hnef
    (actual_closed_fibers_connected_of_affine_formal_functions f hff)

end
end Negativity
