module

public import Negativity.NegativeActualCenter
public import Negativity.ZeroPrimeCurve
public import Negativity.ActualRelativeNef
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- The actual finite coefficient vector of a real Cartier presentation.
Compactness proves finiteness via the actual Cartier support theorem. -/
def actualRealCartierCoefficients
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) : X →₀ ℝ :=
  ∑ t, (cartierOrderDivisor X hn (A t)).mapRange (fun n : ℤ => r t * (n : ℝ)) (by simp)

theorem actualRealCartierCoefficients_apply
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) (x : X) :
    actualRealCartierCoefficients X hn A r x =
      ∑ t, r t * ((A t).coefficient hn x : ℝ) := by
  simp [actualRealCartierCoefficients, cartierOrderDivisor_apply]

/-- Final theorem: actual geometric negativity with a supplied actual
anti-ample witness. The witness's effective coefficients, exceptional
coverage and negative contracted-curve degrees are explicit hypotheses.
Curve existence, actual support and intersections, exceptional-center
identification, and the complete maximum-ratio contradiction are proved.
This does NOT construct E from projectivity or prove geometric ample
positivity, and hence is not the full negativity lemma. -/
theorem actual_negativity_of_antiample_witness
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [CompactSpace X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (d a : τ → ℝ)
    (hpush : CycleEffective (AlgebraicCycle.map f Order.coheight Order.coheight
      (∑ t, (A t).weightedWeilCycle hnX (d t))))
    (hnef : ActualRelativeNef k (f ≫ b) f A (fun t => -d t))
    (hE : ∀ x : X, 0 ≤ ∑ t, a t * ((A t).coefficient hnX x : ℝ))
    (hcover : ∀ x : X, Order.coheight x = 1 →
      (∀ U : Y.Opens, f x ∈ U → ¬ IsIso (f ∣_ U)) →
      0 < ∑ t, a t * ((A t).coefficient hnX x : ℝ))
    (hanti : ∀ (C : Scheme.{u}) [IsIntegral C] (hd : Order.krullDim C = 1)
      (j : C ⟶ X) [IsProper (j ≫ f ≫ b)], IsClosedImmersion j →
      (∀ c : C, f (j c) = f (j (genericPoint C))) →
      normalizedRealCartierCurveIntersection hd k (j ≫ f ≫ b) j A a < 0) :
    ∀ x : X, 0 ≤ ∑ t, d t * ((A t).coefficient hnX x : ℝ) := by
  classical
  let D := actualRealCartierCoefficients X hnX A d
  let E := actualRealCartierCoefficients X hnX A a
  let Dc := ∑ t, (A t).weightedWeilCycle hnX (d t)
  have hDc : ∀ x : X, Dc x = D x := by
    intro x
    simp [Dc, D, actualRealCartierCoefficients_apply,
      CartierAtlas.weightedWeilCycle, CartierAtlas.weilCycle]
  have hnegcenter : ∀ x : X, D x < 0 →
      ∀ U : Y.Opens, f x ∈ U → ¬ IsIso (f ∣_ U) := by
    intro x hx
    exact actual_negative_coefficient_image_in_center f Dc hpush x
      (by rwa [hDc x])
  have hcodim : ∀ x : X, D x < 0 → Order.coheight x = 1 := by
    intro x hx
    by_contra h
    have hall : ∀ t : τ, (A t).coefficient hnX x = 0 := by
      intro t
      simp [CartierAtlas.coefficient, h]
    have hz : D x = 0 := by simp [D, actualRealCartierCoefficients_apply, hall]
    rw [hz] at hx
    exact lt_irrefl _ hx
  have he : Effective E := by
    intro x
    simpa [E, actualRealCartierCoefficients_apply] using hE x
  have hecover : ∀ x : X, D x < 0 → 0 < E x := by
    intro x hx
    simpa [E, actualRealCartierCoefficients_apply] using
      hcover x (hcodim x hx) (hnegcenter x hx)
  suffices hd : Effective D by
    intro x
    simpa [D, actualRealCartierCoefficients_apply] using hd x
  by_contra hneg
  obtain ⟨e, hepos, hshift, η, hηneg, hzero⟩ := exists_effective_shift D E he hecover hneg
  let r : τ → ℝ := fun t => d t + e * a t
  have hr : ∀ x : X, (D + e • E) x = ∑ t, r t * ((A t).coefficient hnX x : ℝ) := by
    intro x
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    simp only [D, E, actualRealCartierCoefficients_apply]
    dsimp [r]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hB : ∀ x : X, 0 ≤ ∑ t, r t * ((A t).coefficient hnX x : ℝ) := by
    intro x
    rw [← hr x]
    exact hshift x
  have hz : (∑ t, r t * ((A t).coefficient hnX η : ℝ)) = 0 := by
    rw [← hr η]
    exact hzero
  obtain ⟨C, j, hC, hdC, hp, hj, hc, _, hnonneg⟩ :=
    zero_exceptional_prime_actual_curve_nonnegative_intersection k b f hf hnX hnY
      η (hcodim η hηneg) (hnegcenter η hηneg) A r hB hz
  have := hC
  have := hp
  have hDneg := (actual_relative_nef_negative_iff k (f ≫ b) f A d).mp hnef
    C hdC j (by simpa only [Scheme.Hom.comp_apply] using hc)
  have hEneg := hanti C hdC j hj hc
  have hlinear : normalizedRealCartierCurveIntersection hdC k (j ≫ f ≫ b) j A r =
      normalizedRealCartierCurveIntersection hdC k (j ≫ f ≫ b) j A d +
        e * normalizedRealCartierCurveIntersection hdC k (j ≫ f ≫ b) j A a := by
    unfold normalizedRealCartierCurveIntersection
    dsimp [r]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hmul := mul_neg_of_pos_of_neg hepos hEneg
  have hDneg' : normalizedRealCartierCurveIntersection hdC k (j ≫ f ≫ b) j A d ≤ 0 := by
    simpa only [← Category.assoc] using hDneg
  rw [hlinear] at hnonneg
  linarith

end
end Negativity
