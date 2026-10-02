module

public import Negativity.RealIntersectionPresentations
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
noncomputable section

/-- Final theorem: an effective actual real Cartier divisor has
nonnegative constructed intersection with a complete normal curve not
contained in its geometric support, and strictly positive intersection
if the curve meets it. Original Cartier weights may have either sign.
The effective decomposition is constructed; presentation independence
identifies its degree with the original actual real intersection. -/
theorem complete_normal_curve_effective_real_cartier_intersection_signs
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    [IsLocallyNoetherian C] [IsLocallyNoetherian X] [CompactSpace X]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (r : τ → ℝ)
    (he : ∀ x : X, 0 ≤ ∑ t, r t * ((A t).coefficient hnX x : ℝ))
    (hη : f (genericPoint C) ∉ closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    0 ≤ realCartierCurveIntersection hnC f A r ∧
      ((f ⁻¹' closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support).Nonempty →
        0 < realCartierCurveIntersection hnC f A r) := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨J, hJ, w, B, hw, hB, _, hEq⟩ :=
    exists_realCartier_effective_weil_decomposition X hnX A r he
  let : Fintype J := hJ
  have hcoeff (x : X) :
      (∑ t, r t * ((A t).coefficient hnX x : ℝ)) =
        ∑ j, w j * ((B j).coefficient hnX x : ℝ) := by
    have h := congrArg (fun D : AlgebraicCycle X ℝ => D x) hEq
    simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply] at h
    change (∑ j, w j * ((B j).coefficient hnX x : ℝ)) =
      ∑ t, r t * ((A t).coefficient hnX x : ℝ) at h
    exact h.symm
  have hI := complete_normal_curve_real_cartier_presentation_independent
    hnC hnX hd k c f A B r w hcoeff
  have hS : closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support =
      ⋃ j : {j : J // 0 < w j}, (B j.1).vanishingSupport := by
    rw [← hEq, effective_cartier_real_sum_support X hnX B w hw hB]
  have havoid (j : J) (hj : 0 < w j) : f (genericPoint C) ∉ (B j).vanishingSupport := by
    intro h
    apply hη
    rw [hS]
    exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, h⟩
  have hterm (j : J) : 0 ≤ w j * (cartierCurveIntersection hnC f (B j) : ℝ) := by
    by_cases hj : w j = 0
    · simp [hj]
    · apply mul_nonneg (hw j)
      exact_mod_cast (complete_normal_curve_effective_cartier_intersection_signs
        hnC hd k c f (B j) (hB j) (havoid j (lt_of_le_of_ne (hw j) (Ne.symm hj)))).1
  rw [hI]
  refine ⟨Finset.sum_nonneg (fun j _ => hterm j), ?_⟩
  rintro ⟨x, hx⟩
  rw [Set.mem_preimage, hS, Set.mem_iUnion] at hx
  obtain ⟨j, hj⟩ := hx
  have hp : 0 < w j.1 * (cartierCurveIntersection hnC f (B j.1) : ℝ) := by
    apply mul_pos j.2
    apply Int.cast_pos.mpr
    exact (complete_normal_curve_effective_cartier_intersection_signs
      hnC hd k c f (B j.1) (hB j.1) (havoid j.1 j.2)).2 ⟨x, hj⟩
  exact Finset.sum_pos' (fun j _ => hterm j) ⟨j.1, Finset.mem_univ _, hp⟩

end
end Negativity
