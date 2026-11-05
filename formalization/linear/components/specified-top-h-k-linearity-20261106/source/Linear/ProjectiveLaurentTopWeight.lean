module
public import Linear.ProjectiveLaurentWeightComponents
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
universe u
variable {σ : Type} [Fintype σ]

/-- In the canonical negative degree, a Laurent weight with every exponent
negative is forced to have every exponent exactly -1. This is the precise
top-residue weight needed for the next actual projective Cech duality step. -/
theorem HomogeneousLaurentExponent.canonical_degree_all_negative_eq_neg_one
    (e : HomogeneousLaurentExponent σ (-(Fintype.card σ : ℤ)))
    (he : ∀ i, e.1 i < 0) : ∀ i, e.1 i = -1 := by
  classical
  have hsum : (∑ i : σ, (e.1 i+1)) = 0 := by
    rw [Finset.sum_add_distrib,← Finsupp.degree_eq_sum e.1,e.property]
    simp
  have hn : ∀ i ∈ (Finset.univ : Finset σ), e.1 i+1 ≤ 0 := by
    intro i hi
    have h := he i
    omega
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hn).mp hsum
  intro i
  have h := hz i (Finset.mem_univ i)
  omega

/-- The actual canonical Laurent exponent (-1,...,-1), with proved total
degree minus the coordinate count. This is exponent data, not a duality proof. -/
def HomogeneousLaurentExponent.canonicalNegative (σ : Type) [Fintype σ] :
    HomogeneousLaurentExponent σ (-(Fintype.card σ : ℤ)) := by
  classical
  let f : σ →₀ ℤ := Finsupp.equivFunOnFinite.symm (fun _ : σ => (-1 : ℤ))
  refine ⟨f,?_⟩
  rw [Finsupp.degree_eq_sum]
  simp [f]

theorem HomogeneousLaurentExponent.canonicalNegative_apply (i : σ) :
    (HomogeneousLaurentExponent.canonicalNegative σ).1 i = -1 := by
  classical
  simp [canonicalNegative]

theorem HomogeneousLaurentExponent.eq_canonicalNegative_of_all_negative
    (e : HomogeneousLaurentExponent σ (-(Fintype.card σ : ℤ)))
    (he : ∀ i, e.1 i < 0) : e = HomogeneousLaurentExponent.canonicalNegative σ := by
  apply Subtype.ext
  ext i
  rw [e.canonical_degree_all_negative_eq_neg_one he,canonicalNegative_apply]

theorem HomogeneousLaurentExponent.canonicalNegative_lifted_support :
    (HomogeneousLaurentExponent.canonicalNegative σ).liftedNegativeSupport =
      (Set.univ : Set (ULift.{u} σ)) := by
  ext i
  simp [liftedNegativeSupport,canonicalNegative_apply]

/-- Every other weight in the canonical degree has a coordinate outside its
negative support, so the already verified Cech contraction applies to it. -/
theorem HomogeneousLaurentExponent.exists_outside_support_of_ne_canonical
    (e : HomogeneousLaurentExponent σ (-(Fintype.card σ : ℤ)))
    (he : e ≠ HomogeneousLaurentExponent.canonicalNegative σ) :
    ∃ i : ULift.{u} σ, i ∉ e.liftedNegativeSupport := by
  classical
  by_contra! h
  apply he
  apply e.eq_canonicalNegative_of_all_negative
  intro i
  have hi := h (ULift.up i)
  exact hi
end MvPolynomial
