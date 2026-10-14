module
public import Linear.ProjectiveLaurentTopWeight
public import Mathlib.Data.Finsupp.Weight
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
variable {σ : Type} [Fintype σ]

/-- The monomial indices of degree m, independent of a coefficient ring. -/
abbrev ProjectiveMonomialIndex (σ : Type) (m : ℕ) :=
  {a : σ →₀ ℕ // a.degree = m}

/-- All-negative Laurent weights at the degree complementary to m. -/
abbrev ProjectiveNegativeWeight (σ : Type) [Fintype σ] (m : ℕ) :=
  {e : HomogeneousLaurentExponent σ (-(m : ℤ) - Fintype.card σ) // ∀ i, e.1 i < 0}

/-- The complementary weight to a monomial a has coordinates -a_i-1. -/
def projectiveMonomialNegativeWeight (m : ℕ) (a : ProjectiveMonomialIndex σ m) :
    ProjectiveNegativeWeight σ m := by
  classical
  let e : σ →₀ ℤ := Finsupp.equivFunOnFinite.symm (fun i => -(a.1 i : ℤ)-1)
  have hd : e.degree = -(m : ℤ)-Fintype.card σ := by
    rw [Finsupp.degree_eq_sum]
    change (∑ i : σ, (-(a.1 i : ℤ)-1)) = -(m : ℤ)-Fintype.card σ
    simp only [Finset.sum_sub_distrib,
      Finset.sum_neg_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    have ha : (∑ i : σ, (a.1 i : ℤ)) = m := by
      exact_mod_cast (Finsupp.degree_eq_sum a.1).symm.trans a.2
    rw [ha]
  refine ⟨⟨e,hd⟩,?_⟩
  intro i
  change -(a.1 i : ℤ)-1 < 0
  omega

theorem projectiveMonomialNegativeWeight_apply (m : ℕ)
    (a : ProjectiveMonomialIndex σ m) (i : σ) :
    (projectiveMonomialNegativeWeight m a).1.1 i = -(a.1 i : ℤ)-1 := rfl

/-- Recover the ordinary monomial exponents from an all-negative weight. -/
def projectiveNegativeWeightMonomial (m : ℕ) (e : ProjectiveNegativeWeight σ m) :
    ProjectiveMonomialIndex σ m := by
  classical
  let a : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (-e.1.1 i-1).toNat)
  refine ⟨a,?_⟩
  have ha (i : σ) : (a i : ℤ) = -e.1.1 i-1 := by
    change ((-e.1.1 i-1).toNat : ℤ) = -e.1.1 i-1
    apply Int.toNat_of_nonneg
    have := e.2 i
    omega
  have hs : (∑ i : σ, (a i : ℤ)) = m := by
    simp only [ha,Finset.sum_sub_distrib,Finset.sum_neg_distrib,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    rw [← Finsupp.degree_eq_sum,e.1.2]
    ring
  rw [Finsupp.degree_eq_sum]
  exact_mod_cast hs

/-- Complementation identifies the two actual finite sets of weights. -/
def projectiveNegativeWeightEquivMonomial (m : ℕ) :
    ProjectiveNegativeWeight σ m ≃ ProjectiveMonomialIndex σ m where
  toFun := projectiveNegativeWeightMonomial m
  invFun := projectiveMonomialNegativeWeight m
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    change -(((-e.1.1 i-1).toNat : ℕ) : ℤ)-1 = e.1.1 i
    rw [Int.toNat_of_nonneg (by have := e.2 i; omega)]
    ring
  right_inv a := by
    apply Subtype.ext
    ext i
    change (-(-(a.1 i : ℤ)-1)-1).toNat = a.1 i
    have h : -(-(a.1 i : ℤ)-1)-1 = a.1 i := by ring
    rw [h,Int.toNat_natCast]

instance projectiveMonomialIndexFinite (m : ℕ) : Finite (ProjectiveMonomialIndex σ m) :=
  (Finsupp.finite_of_degree_eq (σ := σ) m).to_subtype

instance projectiveNegativeWeightFinite (m : ℕ) : Finite (ProjectiveNegativeWeight σ m) :=
  Finite.of_injective (projectiveNegativeWeightEquivMonomial m)
    (projectiveNegativeWeightEquivMonomial m).injective
end MvPolynomial
