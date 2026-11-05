module
public import Linear.ProjectiveLaurentWeightComponents
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
universe u
variable {σ : Type} [Fintype σ]

/-- For ORIGINAL finite homogeneous Laurent weights,all negative
exponents force the ORIGINAL total degree to be at most -card(sigma). -/
theorem HomogeneousLaurentExponent.degree_le_neg_card_of_all_negative
    {d : ℤ} (e : HomogeneousLaurentExponent σ d) (he : ∀ i, e.1 i < 0) :
    d ≤ -(Fintype.card σ:ℤ) := by
  classical
  have hsum : (∑ i : σ, e.1 i) ≤ ∑ _i : σ, (-1:ℤ) :=
    Finset.sum_le_sum (fun i _ => by have hi := he i; omega)
  rw [← Finsupp.degree_eq_sum,e.property] at hsum
  simpa using hsum

/-- If the ORIGINAL integer twist degree exceeds -card(sigma),every
actual Laurent weight has a coordinate outside its ORIGINAL negative
support. This covers the intermediate NEGATIVE twists too. -/
theorem HomogeneousLaurentExponent.exists_not_mem_liftedNegativeSupport_of_gt_neg_card
    {d : ℤ} (e : HomogeneousLaurentExponent σ d) (hd : -(Fintype.card σ:ℤ)<d) :
    ∃ i : ULift.{u} σ, i ∉ e.liftedNegativeSupport := by
  classical
  by_contra! h
  have he : ∀ i : σ, e.1 i < 0 := fun i => h (ULift.up i)
  exact (not_le_of_gt hd) (e.degree_le_neg_card_of_all_negative he)

end MvPolynomial
