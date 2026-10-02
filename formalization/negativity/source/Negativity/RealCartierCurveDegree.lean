module

public import Negativity.CartierCurveRestriction
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Degree signs for a nonnegative real combination of actual effective
Cartier divisors, restricted to an integral normal curve not contained in
its geometric support. Zero-weight terms are omitted, so they impose no
unnecessary generic-point avoidance condition. The restricted divisors,
support equality and order-sum inequalities are all outputs. -/
theorem effective_real_cartier_curve_order_signs {C X : Scheme}
    [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C] [IsLocallyNoetherian X]
    [CompactSpace C]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : C ⟶ X) {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (c : τ → ℝ)
    (hc : ∀ t, 0 ≤ c t) (hA : ∀ t, (A t).Effective)
    (hη : f (genericPoint C) ∉ closure (∑ t, (A t).weightedWeilCycle hnX (c t)).support) :
    ∃ B : {t : τ // 0 < c t} → CartierAtlas C C,
      (∀ t, (B t).Effective) ∧
      (⋃ t, (B t).vanishingSupport) =
        f ⁻¹' closure (∑ t, (A t).weightedWeilCycle hnX (c t)).support ∧
      0 ≤ ∑ t, c t.1 * (cartierTotalOrder C hnC (B t) : ℝ) ∧
      ((f ⁻¹' closure (∑ t, (A t).weightedWeilCycle hnX (c t)).support).Nonempty →
        0 < ∑ t, c t.1 * (cartierTotalOrder C hnC (B t) : ℝ)) := by
  classical
  have hS := effective_cartier_real_sum_support X hnX A c hc hA
  have havoid (t : {t : τ // 0 < c t}) :
      f (genericPoint C) ∉ (A t.1).vanishingSupport := by
    intro h
    apply hη
    rw [hS]
    exact Set.mem_iUnion.mpr ⟨t, h⟩
  choose B hBe hBs hBn hBp using fun t : {t : τ // 0 < c t} =>
    effective_cartier_restriction_order_signs hnC f (A t.1) (hA t.1) (havoid t)
  have hsupport : (⋃ t, (B t).vanishingSupport) =
      f ⁻¹' closure (∑ t, (A t).weightedWeilCycle hnX (c t)).support := by
    simp_rw [hBs]
    rw [← Set.preimage_iUnion, ← hS]
  have hterm (t : {t : τ // 0 < c t}) :
      0 ≤ c t.1 * (cartierTotalOrder C hnC (B t) : ℝ) :=
    mul_nonneg (le_of_lt t.2) (by exact_mod_cast hBn t)
  refine ⟨B, hBe, hsupport, Finset.sum_nonneg (fun t _ => hterm t), ?_⟩
  intro hmeet
  obtain ⟨x, hx⟩ := hmeet
  rw [← hsupport, Set.mem_iUnion] at hx
  obtain ⟨t, ht⟩ := hx
  have hpos : 0 < c t.1 * (cartierTotalOrder C hnC (B t) : ℝ) := by
    apply mul_pos t.2
    apply Int.cast_pos.mpr
    apply hBp t
    exact ⟨x, hBs t ▸ ht⟩
  exact Finset.sum_pos' (fun t _ => hterm t) ⟨t, Finset.mem_univ t, hpos⟩

/-- Original real weights may have either sign. An effective actual real
Weil sum is first decomposed by the proved rational-cone construction,
then each positive-weight effective Cartier term is restricted to C.
This proves degree signs for the constructed effective presentation;
it does not assert degree independence under arbitrary presentations. -/
theorem effective_realCartier_curve_decomposition_order_signs {C X : Scheme}
    [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C] [IsLocallyNoetherian X]
    [CompactSpace C] [CompactSpace X]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : C ⟶ X) {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (c : τ → ℝ)
    (he : ∀ x : X, 0 ≤ ∑ t, c t * ((A t).coefficient hnX x : ℝ))
    (hη : f (genericPoint C) ∉ closure (∑ t, (A t).weightedWeilCycle hnX (c t)).support) :
    ∃ (J : Type) (_ : Fintype J) (w : J → ℝ) (B : J → CartierAtlas X X)
      (R : {j : J // 0 < w j} → CartierAtlas C C),
      (∀ j, 0 ≤ w j) ∧ (∀ j, (B j).Effective) ∧
      (∑ j, (B j).weightedWeilCycle hnX (w j)) =
        ∑ t, (A t).weightedWeilCycle hnX (c t) ∧
      (∀ j, (R j).Effective) ∧
      (⋃ j, (R j).vanishingSupport) =
        f ⁻¹' closure (∑ t, (A t).weightedWeilCycle hnX (c t)).support ∧
      0 ≤ ∑ j, w j.1 * (cartierTotalOrder C hnC (R j) : ℝ) ∧
      ((f ⁻¹' closure (∑ t, (A t).weightedWeilCycle hnX (c t)).support).Nonempty →
        0 < ∑ j, w j.1 * (cartierTotalOrder C hnC (R j) : ℝ)) := by
  classical
  obtain ⟨J, hJ, w, B, hw, hB, _, hEq⟩ :=
    exists_realCartier_effective_weil_decomposition X hnX A c he
  let : Fintype J := hJ
  have hηB : f (genericPoint C) ∉ closure (∑ j, (B j).weightedWeilCycle hnX (w j)).support := by
    rw [hEq]
    exact hη
  obtain ⟨R, hR, hS, hn, hp⟩ :=
    effective_real_cartier_curve_order_signs hnC hnX f B w hw hB hηB
  rw [hEq] at hS hp
  exact ⟨J, hJ, w, B, R, hw, hB, hEq, hR, hS, hn, hp⟩

end Negativity
