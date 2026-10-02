module

public import Negativity.CurveCartierFiber
public import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A finite-support pushforward coefficient is the sum over its actual fiber. -/
theorem finsupp_mapDomain_actual_fiber {α β : Type*} (f : α → β) (D : α →₀ ℤ)
    (y : β) [Fintype {x : α // f x = y}] :
    D.mapDomain f y = ∑ x : {x : α // f x = y}, D x := by
  classical
  calc
    _ = ∑ x ∈ D.support with f x = y, D x := by
      simp [Finsupp.mapDomain, Finsupp.sum, Finsupp.single_apply, Finset.sum_ite]
    _ = ∑ x ∈ D.support.subtype (fun x => f x = y), D x :=
      (Finset.sum_subtype_eq_sum_filter (fun x => D x)).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      apply Finsupp.notMem_support_iff.mp
      simpa only [Finset.mem_subtype] using hx

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdX : Order.krullDim X ≤ 1) (hdY : Order.krullDim Y ≤ 1)

local instance (y : Y) : Fintype {x : X // f x = y} := by
  change Fintype (f ⁻¹' {y})
  exact (f.finite_preimage_singleton y).fintype

include k b hdX hdY

/-- Actual Cartier divisor push-pull along a finite dominant normal-curve
morphism, with the full function-field degree. -/
theorem finite_normal_curve_cartier_push_pull {ι : Type*} (A : CartierAtlas Y ι) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    ∃ B : CartierAtlas X X,
      (∀ z : X, B.chart z ≤ f ⁻¹ᵁ A.chart (A.covers (f z)).choose ∧ z ∈ B.chart z ∧
        B.equation z = Units.map (dominantFunctionFieldMap f).toMonoidHom
          (A.equation (A.covers (f z)).choose)) ∧
      (cartierOrderDivisor X hnX B).mapDomain f =
        (Module.finrank Y.functionField X.functionField : ℤ) • cartierOrderDivisor Y hnY A := by
  classical
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  obtain ⟨B, hdata, hB⟩ := finite_normal_curve_cartier_fiber_orders f k b hnX hnY hdX hdY A
  refine ⟨B, hdata, ?_⟩
  ext y
  rw [finsupp_mapDomain_actual_fiber]
  change (∑ x : {x : X // f x = y}, B.coefficient hnX x) =
    (Module.finrank Y.functionField X.functionField : ℤ) * A.coefficient hnY y
  by_cases hy : Order.coheight y = 1
  · exact (hB y hy).trans (mul_comm _ _)
  · have hAy : A.coefficient hnY y = 0 := by simp [CartierAtlas.coefficient, hy]
    rw [hAy, mul_zero]
    apply Finset.sum_eq_zero
    intro x _
    have hx : Order.coheight (x : X) ≠ 1 := by
      intro hxc
      have he := finite_normal_curve_maps_coheight_one f hnX hnY hdX hdY x hxc
      exact hy (x.2 ▸ he)
    simp [CartierAtlas.coefficient, hx]

/-- Final theorem: global degree of the actual Cartier pullback is the full
function-field degree times the target Cartier degree. Finite support,
actual fibers, their local-order compatibility and all residue weights
are proved; no global projection or degree identity is an input.
This statement covers arbitrary characteristic and inseparable maps. -/
theorem finite_normal_curve_cartier_pullback_degree {ι : Type*} (A : CartierAtlas Y ι) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    ∃ B : CartierAtlas X X,
      (∀ z : X, B.chart z ≤ f ⁻¹ᵁ A.chart (A.covers (f z)).choose ∧ z ∈ B.chart z ∧
        B.equation z = Units.map (dominantFunctionFieldMap f).toMonoidHom
          (A.equation (A.covers (f z)).choose)) ∧
      cartierTotalOrder X hnX B =
      (Module.finrank Y.functionField X.functionField : ℤ) * cartierTotalOrder Y hnY A := by
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  obtain ⟨B, hdata, hB⟩ := finite_normal_curve_cartier_push_pull f k b hnX hnY hdX hdY A
  refine ⟨B, hdata, ?_⟩
  have he := congrArg Finsupp.degree hB
  rw [Finsupp.degree_mapDomain, map_zsmul] at he
  unfold cartierTotalOrder
  simpa only [Finsupp.degree_apply, Finsupp.sum, zsmul_eq_mul, Int.cast_id] using he

end
end Negativity
