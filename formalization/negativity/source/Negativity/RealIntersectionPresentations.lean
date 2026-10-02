module

public import Negativity.RealCurveIntersection
public import Negativity.CartierReindex
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
noncomputable section

/-- Final theorem: two arbitrary finite real Cartier presentations with
the same actual ambient Weil coefficients have the same constructed
complete-normal-curve intersection. Both the generators and their affine
chart index types may differ. The common family is built from actual
point-indexed Cartier charts; cover and real-kernel invariance are proved,
not assumed. Arbitrary characteristic is retained. -/
theorem complete_normal_curve_real_cartier_presentation_independent
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    [IsLocallyNoetherian C] [IsLocallyNoetherian X]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι κ τ σ : Type*} [Fintype τ] [Fintype σ]
    (A : τ → CartierAtlas X ι) (B : σ → CartierAtlas X κ)
    (r : τ → ℝ) (s : σ → ℝ)
    (heq : ∀ x : X,
      (∑ t, r t * ((A t).coefficient hnX x : ℝ)) =
        ∑ j, s j * ((B j).coefficient hnX x : ℝ)) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    realCartierCurveIntersection hnC f A r = realCartierCurveIntersection hnC f B s := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  let D : τ ⊕ σ → CartierAtlas X X := Sum.elim
    (fun t => (A t).pointIndexed) (fun j => (B j).pointIndexed)
  let w : τ ⊕ σ → ℝ := Sum.elim r (fun j => -s j)
  have hz (x : X) : ∑ t, w t * ((D t).coefficient hnX x : ℝ) = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [D, w, Sum.elim_inl, Sum.elim_inr, cartierAtlas_pointIndexed_coefficient,
      neg_mul, Finset.sum_neg_distrib]
    rw [heq x, add_neg_cancel]
  have h := complete_normal_curve_cartier_real_relation hnC hnX hd k c f D w hz
  unfold realCartierCurveIntersection at h ⊢
  rw [Fintype.sum_sum_type] at h
  simp only [D, w, Sum.elim_inl, Sum.elim_inr,
    complete_normal_curve_cartier_intersection_pointIndexed hnC hd k c f,
    neg_mul, Finset.sum_neg_distrib] at h
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)

end
end Negativity
