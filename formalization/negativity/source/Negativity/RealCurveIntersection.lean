module

public import Negativity.CurveCartierCombinations
public import Negativity.CartierZeroIntersection
public import Negativity.RealCartierPullback
public import Negativity.RationalCone
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
noncomputable section

/-- The real extension of actual integer Cartier curve intersections.
The generators are genuine ambient Cartier atlases, not numerical input. -/
def realCartierCurveIntersection
    {C X : Scheme} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C]
    [CompactSpace C] (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (f : C ⟶ X) {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (r : τ → ℝ) : ℝ :=
  ∑ t, r t * (cartierCurveIntersection hn f (A t) : ℝ)

/-- Actual integer relations between ambient Weil coefficients induce
integer relations between the constructed complete-curve intersections. -/
theorem complete_normal_curve_cartier_integral_relation
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    [IsLocallyNoetherian C] [IsLocallyNoetherian X]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (n : τ → ℤ)
    (hz : ∀ x : X, ∑ t, n t * (A t).coefficient hnX x = 0) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    (∑ t, n t * cartierCurveIntersection hnC f (A t)) = 0 := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨D, hD, hI⟩ :=
    exists_complete_curve_cartier_intersection_integralCombination hnC hd k c f A n
  have hcoeff := cartierAtlas_integralCombination_coefficients X hnX A n D
    (fun x => ⟨(hD x).1, (hD x).2.2⟩)
  have hzero := complete_normal_curve_zero_cartier_intersection hnC hnX hd k c f D
    (fun x => (hcoeff x).trans (hz x))
  rwa [hI] at hzero

/-- Clear denominators in a rational Weil relation, using actual integer
Cartier combinations and their already constructed intersections. -/
theorem complete_normal_curve_cartier_rational_relation
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    [IsLocallyNoetherian C] [IsLocallyNoetherian X]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (q : τ → ℚ)
    (hz : ∀ x : X, ∑ t, q t * ((A t).coefficient hnX x : ℚ) = 0) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    realCartierCurveIntersection hnC f A (fun t => (q t : ℝ)) = 0 := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨N, n, hN, hn⟩ := rational_vector_positive_integer_multiple q
  have hn' (t : τ) : (n t : ℝ) = (N : ℝ) * (q t : ℝ) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hn t
  have hz' (x : X) : ∑ t, n t * (A t).coefficient hnX x = 0 := by
    have hr : ∑ t, (q t : ℝ) * ((A t).coefficient hnX x : ℝ) = 0 := by
      exact_mod_cast hz x
    have hs : ∑ t, (n t : ℝ) * ((A t).coefficient hnX x : ℝ) = 0 := by
      simp_rw [hn', mul_assoc]
      rw [← Finset.mul_sum, hr, mul_zero]
    exact_mod_cast hs
  have hi : ∑ t, (n t : ℝ) * (cartierCurveIntersection hnC f (A t) : ℝ) = 0 := by
    exact_mod_cast complete_normal_curve_cartier_integral_relation hnC hnX hd k c f A n hz'
  simp_rw [hn', mul_assoc] at hi
  rw [← Finset.mul_sum] at hi
  exact (mul_eq_zero.mp hi).resolve_left (by exact_mod_cast (Nat.ne_zero_of_lt hN))

/-- Arbitrary real relations are spanned by rational relations because
all actual ambient Weil coefficients are integers. No finite global
support or real-relation descent premise is assumed. -/
theorem complete_normal_curve_cartier_real_relation
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    [IsLocallyNoetherian C] [IsLocallyNoetherian X]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (r : τ → ℝ)
    (hz : ∀ x : X, ∑ t, r t * ((A t).coefficient hnX x : ℝ) = 0) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    realCartierCurveIntersection hnC f A r = 0 := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  let M (t : τ) (x : X) : ℚ := (A t).coefficient hnX x
  obtain ⟨n, w, q, heq, hq⟩ := rational_parameterization_preserves_zero M r
  have hqz (j : Fin n) : ∀ x : X, ∑ t, q j t * ((A t).coefficient hnX x : ℚ) = 0 := by
    intro x
    apply hq x
    simpa [rationalCoefficientMap, M] using hz x
  have hIq (j : Fin n) :=
    complete_normal_curve_cartier_rational_relation hnC hnX hd k c f A (q j) (hqz j)
  rw [← heq]
  unfold realCartierCurveIntersection
  change (∑ t, (∑ j, w j * (q j t : ℝ)) *
    (cartierCurveIntersection hnC f (A t) : ℝ)) = 0
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  change w j * realCartierCurveIntersection hnC f A (fun t => (q j t : ℝ)) = 0
  rw [hIq j, mul_zero]

/-- Final theorem: the actual real intersection is independent of the
real coefficient vector whenever it represents the same actual ambient
Weil coefficients in a finite family of genuine Cartier generators.
The entire real kernel statement is derived from local orders, actual
integer combinations, and rational linear algebra. Arbitrary characteristic
is retained; normalization of a nonnormal curve is a separate task. -/
theorem complete_normal_curve_real_cartier_intersection_wellDefined
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    [IsLocallyNoetherian C] [IsLocallyNoetherian X]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (r s : τ → ℝ)
    (heq : ∀ x : X,
      (∑ t, r t * ((A t).coefficient hnX x : ℝ)) =
        ∑ t, s t * ((A t).coefficient hnX x : ℝ)) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    realCartierCurveIntersection hnC f A r = realCartierCurveIntersection hnC f A s := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  have hz (x : X) : ∑ t, (r t - s t) * ((A t).coefficient hnX x : ℝ) = 0 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, heq x, sub_self]
  have h := complete_normal_curve_cartier_real_relation hnC hnX hd k c f A (r - s) hz
  unfold realCartierCurveIntersection at h ⊢
  simpa only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using h

end
end Negativity
