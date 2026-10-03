module

public import Negativity.NormalizedCurveIntersection
public import Negativity.CartierCombinations
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Actual negative Cartier divisor, using inverse local equations and
inverse actual stalk transition units. -/
def CartierAtlas.inverse {X : Scheme} [IsIntegral X] {ι : Type*}
    (A : CartierAtlas X ι) : CartierAtlas X ι where
  chart := A.chart
  affine := A.affine
  nonempty := A.nonempty
  covers := A.covers
  equation := fun i => (A.equation i)⁻¹
  transition := by
    intro i j x hi hj
    obtain ⟨v, hv⟩ := A.transition i j x hi hj
    refine ⟨v⁻¹, ?_⟩
    rw [map_inv, ← hv, mul_inv_rev]
    exact mul_comm _ _

theorem cartierAtlas_inverse_coefficient
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) (x : X) :
    A.inverse.coefficient hn x = -A.coefficient hn x := by
  classical
  by_cases hx : Order.coheight x = 1
  · let i := (A.covers x).choose
    have hi : x ∈ A.chart i := (A.covers x).choose_spec
    rw [cartierAtlas_coefficient_eq X hn A.inverse i x hx hi,
      cartierAtlas_coefficient_eq X hn A i x hx hi]
    have := hn x
    have := normal_codimensionOne_stalk_isDVR X x hx
    unfold schemeRationalOrder
    simpa [CartierAtlas.inverse] using
      dvr_rationalOrder_zpow (X.presheaf.stalk x) X.functionField (A.equation i) (-1)
  · simp [CartierAtlas.coefficient, hx]

/-- Final theorem: negating an actual ambient Cartier divisor negates
its actual normalized intersection on every complete integral curve.
This follows from proved real presentation independence, not from an
assumed linear intersection functional. -/
theorem complete_integral_curve_cartier_intersection_inverse
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian X]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι) :
    normalizedCartierCurveIntersection hd k c f A.inverse =
      -normalizedCartierCurveIntersection hd k c f A := by
  have hi := complete_integral_curve_real_cartier_presentation_independent
    hnX hd k c f (fun _ : Unit => A.inverse) (fun _ : Unit => A)
    (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ)) (by
      intro x
      simp [cartierAtlas_inverse_coefficient])
  have he : (normalizedCartierCurveIntersection hd k c f A.inverse : ℝ) =
      -(normalizedCartierCurveIntersection hd k c f A : ℝ) := by
    simpa [normalizedRealCartierCurveIntersection] using hi
  exact_mod_cast he

end
end Negativity
