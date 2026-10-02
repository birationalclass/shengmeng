module

public import Negativity.ExceptionalCompleteCurve
public import Negativity.CurveSelection
public import Negativity.NormalizedIntersectionSigns
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem zero_weil_coefficient_outside_geometric_support
    (X : Scheme.{u}) [CompactSpace X] (B : AlgebraicCycle X ℝ)
    (hB : AlgebraicCycle.IsWeilDivisor B) (η : X) (hη : Order.coheight η = 1)
    (hzero : B η = 0) : η ∉ closure B.support := by
  classical
  intro hm
  have he : B.support = ⋃ z ∈ B.support, ({z} : Set X) := by ext; simp
  rw [he, B.finite_support.closure_biUnion] at hm
  obtain ⟨z, hzs, hcl⟩ := Set.mem_iUnion₂.mp hm
  have hz : Order.coheight z = 1 := hB hzs
  have hle : η ≤ z := specializes_iff_mem_closure.mpr hcl
  have hge : z ≤ η := by
    by_contra hn
    have ht := Order.coheight_strictAnti (show η < z from ⟨hle, hn⟩)
      (by rw [hz]; exact ENat.one_lt_top)
    rw [hz, hη] at ht
    exact lt_irrefl _ ht
  have hηz : η = z := (Specializes.antisymm hge hle).eq
  exact hzs (hηz ▸ hzero)

/-- Final theorem: an effective actual real Cartier divisor whose
coefficient at an exceptional prime is zero admits an actual complete
contracted curve outside its support with nonnegative actual intersection.
The closed point, curve and generic avoidance are all constructed. -/
theorem zero_exceptional_prime_actual_curve_nonnegative_intersection
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [CompactSpace X]
    [IsLocallyNoetherian X]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (η : X) (hη : Order.coheight η = 1)
    (hcenter : ∀ U : Y.Opens, f η ∈ U → ¬ IsIso (f ∣_ U))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ)
    (he : ∀ x : X, 0 ≤ ∑ t, r t * ((A t).coefficient hnX x : ℝ))
    (hzero : (∑ t, r t * ((A t).coefficient hnX η : ℝ)) = 0) :
    ∃ (C : Scheme.{u}) (j : C ⟶ X) (hC : IsIntegral C) (hdC : Order.krullDim C = 1)
      (hp : IsProper (j ≫ f ≫ b)), IsClosedImmersion j ∧
      (∀ c : C, f (j c) = f (j (genericPoint C))) ∧
      j (genericPoint C) ∉ closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support ∧
      0 ≤ normalizedRealCartierCurveIntersection hdC k (j ≫ f ≫ b) j A r := by
  classical
  let B := ∑ t, (A t).weightedWeilCycle hnX (r t)
  have hB : AlgebraicCycle.IsWeilDivisor B := by
    intro z hz
    by_contra hc
    change Order.coheight z ≠ 1 at hc
    have hall : ∀ t : τ, (A t).coefficient hnX z = 0 := by
      intro t
      simp [CartierAtlas.coefficient, hc]
    exact hz (by simp [B, CartierAtlas.weightedWeilCycle, CartierAtlas.weilCycle, hall])
  have hηS : η ∉ closure B.support :=
    zero_weil_coefficient_outside_geometric_support X B hB η hη
      (by simpa [B, CartierAtlas.weightedWeilCycle, CartierAtlas.weilCycle] using hzero)
  have hnot : ¬ closure ({η} : Set X) ⊆ closure B.support :=
    fun h => hηS (h (subset_closure (Set.mem_singleton η)))
  obtain ⟨x, hxF, hxS, hxc⟩ := finiteType_exists_closedPoint_outside_support k X (f ≫ b)
    (closure {η}) (closure B.support) isClosed_closure isClosed_closure hnot
  have hcX : ∀ U : Y.Opens, f x ∈ U → ¬ IsIso (f ∣_ U) := by
    intro U hxU
    apply hcenter U
    exact (f.continuous.specialization_monotone
      (specializes_iff_mem_closure.mpr hxF)).mem_open U.isOpen hxU
  obtain ⟨C, j, hC, hdC, hj, hp, hxj, hconst⟩ :=
    exceptional_closed_point_complete_contracted_curve k b f hf hnY x hxc hcX
  have := hC
  have := hp
  obtain ⟨c, hc⟩ := hxj
  have hgen : j (genericPoint C) ∉ closure B.support := by
    intro hm
    have hsp : j (genericPoint C) ⤳ j c :=
      j.continuous.specialization_monotone ((genericPoint_spec C).specializes trivial)
    exact hxS (hc ▸ hsp.mem_closed isClosed_closure hm)
  refine ⟨C, j, hC, hdC, hp, hj, fun c => (hconst c).trans (hconst _).symm, hgen, ?_⟩
  exact (complete_integral_curve_effective_real_intersection_signs hnX hdC k
    (j ≫ f ≫ b) j A r he hgen).1

end
end Negativity
