module

public import Negativity.ConnectedCurveCrossing
public import Negativity.ActualRelativeNef
public import Negativity.NormalizedIntersectionSigns
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: an actual connected complete scheme contracted by f
is either disjoint from or wholly mapped into the actual support of an
effective real Cartier divisor with negative relative nefness. All
curve selection and actual positive intersection are proved. This
does not derive connectedness of the fibers of proper birational f. -/
theorem actual_connected_contracted_scheme_support_dichotomy
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) (f : X ⟶ Y)
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ)
    (he : ∀ x : X, 0 ≤ ∑ t, r t * ((A t).coefficient hnX x : ℝ))
    (hnef : ActualRelativeNef k (f ≫ b) f A (fun t => -r t))
    (Z : Scheme.{u}) [ConnectedSpace Z] (i : Z ⟶ X) [IsProper (i ≫ f ≫ b)]
    (hcontract : ∀ z w : Z, f (i z) = f (i w)) :
    (∀ z : Z, i z ∉ closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support) ∨
      (∀ z : Z, i z ∈ closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support) := by
  classical
  let S := closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support
  let T : Set Z := i ⁻¹' S
  have hT : IsClosed T := isClosed_closure.preimage i.continuous
  by_cases hnone : ∀ z : Z, i z ∉ S
  · exact Or.inl hnone
  right
  by_contra hn
  have hne : T.Nonempty := by
    simpa only [T, Set.nonempty_def, Set.mem_preimage, not_forall, not_not] using hnone
  have hnall : ¬ Set.univ ⊆ T := by
    intro hall
    exact hn (fun z => hall trivial)
  obtain ⟨C, j, hC, hdC, hj, hp, hmeet, havoid⟩ :=
    connected_complete_scheme_actual_crossing_curve Z k (i ≫ f ≫ b) T hT hne hnall
  have := hC
  have := hj
  have := hp
  have hpC : IsProper ((j ≫ i) ≫ (f ≫ b)) := by
    simpa only [Category.assoc] using hp
  have hη : (j ≫ i) (genericPoint C) ∉ S := by
    intro hm
    apply havoid
    rintro _ ⟨c, rfl⟩
    have hsp : i (j (genericPoint C)) ⤳ i (j c) :=
      (j ≫ i).continuous.specialization_monotone ((genericPoint_spec C).specializes trivial)
    exact hsp.mem_closed isClosed_closure hm
  have hconst : ∀ c : C, ((j ≫ i) ≫ f) c = ((j ≫ i) ≫ f) (genericPoint C) := by
    intro c
    simp only [Scheme.Hom.comp_apply]
    exact hcontract (j c) (j (genericPoint C))
  have hnonpos := (actual_relative_nef_negative_iff k (f ≫ b) f A r).mp hnef
    C hdC (j ≫ i) hconst
  have hmeets : ((j ≫ i) ⁻¹' S).Nonempty := by
    obtain ⟨z, ⟨c, hc⟩, hzT⟩ := hmeet
    refine ⟨c, ?_⟩
    change i (j c) ∈ S
    rw [hc]
    exact hzT
  have hpos := (complete_integral_curve_effective_real_intersection_signs hnX hdC k
    ((j ≫ i) ≫ (f ≫ b)) (j ≫ i) A r he hη).2 hmeets
  exact (not_lt_of_ge hnonpos) hpos

end
end Negativity
