module

public import Negativity.CartierVanishing
public import Negativity.FunctionFieldProductFormula
public import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Finite divisor obtained from the actual Cartier equations. Global
finiteness is proved from quasi-compactness and local coefficient finiteness. -/
noncomputable def cartierOrderDivisor (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) : X →₀ ℤ :=
  Finsupp.ofSupportFinite (A.coefficient hn) (cartierAtlas_weilCycle_finite_support X hn A)

theorem cartierOrderDivisor_apply (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) (x : X) :
    cartierOrderDivisor X hn A x = A.coefficient hn x := rfl

/-- On a normal curve over an algebraically closed field, degree is the
sum of its Cartier local orders (all closed-point residue degrees are one).
The same sum is defined for any quasi-compact normal scheme; it is NOT
claimed to be geometric divisor degree in higher dimension. -/
noncomputable def cartierTotalOrder (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) : ℤ :=
  (cartierOrderDivisor X hn A).sum (fun _ n => n)

/-- Cover refinement and multiplication by actual local units leave the
order sum unchanged. No coefficient-equality premise is needed. -/
theorem cartierTotalOrder_eq_of_unit_transitions (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι κ : Type*} (A : CartierAtlas X ι) (B : CartierAtlas X κ)
    (h : ∀ i j (x : X), x ∈ A.chart i → x ∈ B.chart j →
      ∃ u : (X.presheaf.stalk x)ˣ,
        Units.map (algebraMap (X.presheaf.stalk x) X.functionField : _ →* _) u *
          A.equation i = B.equation j) :
    cartierTotalOrder X hn A = cartierTotalOrder X hn B := by
  have he := cartierAtlas_weilCycle_eq_of_unit_transitions X hn A B h
  have hd : cartierOrderDivisor X hn A = cartierOrderDivisor X hn B := by
    ext x
    exact congrArg (fun c : AlgebraicCycle X ℤ => c x) he
  unfold cartierTotalOrder
  rw [hd]

theorem effective_cartierTotalOrder_nonneg (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) (hA : A.Effective) :
    0 ≤ cartierTotalOrder X hn A := by
  apply Finsupp.sum_nonneg
  intro x _
  exact effective_cartierAtlas_weil_nonneg X hn A hA x

/-- A nonzero effective Cartier divisor has strictly positive order sum. -/
theorem effective_cartierTotalOrder_pos (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) (hA : A.Effective)
    (hD : ∃ x : X, A.coefficient hn x ≠ 0) :
    0 < cartierTotalOrder X hn A := by
  apply Finsupp.sum_pos
  · intro x hx
    have hn0 := effective_cartierAtlas_weil_nonneg X hn A hA x
    have hn1 : A.coefficient hn x ≠ 0 := Finsupp.mem_support_iff.mp hx
    exact lt_of_le_of_ne hn0 (Ne.symm hn1)
  · intro hz
    obtain ⟨x, hx⟩ := hD
    have he := congrArg (fun d : X →₀ ℤ => d x) hz
    exact hx he

/-- Geometric full support nonemptiness supplies the nonzero coefficient
needed for strict positivity, using the proved support-closure theorem. -/
theorem effective_cartierTotalOrder_pos_of_support (X : Scheme) [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) (hA : A.Effective)
    (hS : A.vanishingSupport.Nonempty) :
    0 < cartierTotalOrder X hn A := by
  apply effective_cartierTotalOrder_pos X hn A hA
  by_contra! h
  have hz : (A.weilCycle hn).support = ∅ := by
    ext x
    simp [h, CartierAtlas.weilCycle]
  rw [cartierAtlas_vanishingSupport_eq_closure_weilSupport X hn A, hz, closure_empty] at hS
  exact Set.not_nonempty_empty hS

end Negativity
