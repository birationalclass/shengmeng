module

public import Negativity.EffectiveCurveIntersection
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem cartier_support_empty_of_coefficients_zero (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) (hA : ∀ x : X, A.coefficient hn x = 0) :
    A.vanishingSupport = ∅ := by
  rw [cartierAtlas_vanishingSupport_eq_closure_weilSupport X hn A]
  have hs : (A.weilCycle hn).support = ∅ := by
    ext x
    simp [CartierAtlas.weilCycle, hA]
  rw [hs, closure_empty]

theorem cartierTotalOrder_zero_of_support_empty (C : Scheme) [IsIntegral C]
    [IsLocallyNoetherian C] [CompactSpace C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    {ι : Type*} (B : CartierAtlas C ι) (hB : B.vanishingSupport = ∅) :
    cartierTotalOrder C hn B = 0 := by
  have hc (x : C) : B.coefficient hn x = 0 := by
    by_contra hx
    have hm : x ∈ closure (B.weilCycle hn).support := subset_closure hx
    rw [← cartierAtlas_vanishingSupport_eq_closure_weilSupport C hn B, hB] at hm
    exact hm
  unfold cartierTotalOrder Finsupp.sum
  apply Finset.sum_eq_zero
  intro x _
  exact hc x

/-- Final theorem: if an actual Cartier divisor has zero actual Weil
coefficients on a normal locally Noetherian integral ambient Scheme, its
constructed intersection with every actual complete normal curve is zero.
Normality derives empty full support and genuine regular restriction;
neither support emptiness nor an intersection identity is assumed. -/
theorem complete_normal_curve_zero_cartier_intersection
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    [IsLocallyNoetherian C] [IsLocallyNoetherian X]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι)
    (hA : ∀ x : X, A.coefficient hnX x = 0) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    cartierCurveIntersection hnC f A = 0 := by
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  have hs := cartier_support_empty_of_coefficients_zero X hnX A hA
  have hAe : A.Effective := (cartierAtlas_effective_iff_weil_nonneg X hnX A).mpr
    (fun x => by change 0 ≤ A.coefficient hnX x; rw [hA x])
  have hη : f (genericPoint C) ∉ A.vanishingSupport := by simp [hs]
  obtain ⟨B, hdata, _, hS⟩ := effective_cartier_restriction_with_data f A hAe hη
  rw [complete_normal_curve_cartier_intersection_eq_restriction hnC hd k c f A 1 B hdata]
  apply cartierTotalOrder_zero_of_support_empty C hnC B
  rw [hS, hs, Set.preimage_empty]

end
end Negativity
