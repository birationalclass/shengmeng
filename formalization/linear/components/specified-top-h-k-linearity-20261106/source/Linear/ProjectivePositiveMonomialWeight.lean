module
public import Linear.ProjectiveHomogeneousBasisProduct
public import Linear.ProjectiveLaurentNatExponent
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
variable {σ : Type} [Fintype σ]

/-- Original natural monomial exponents, regarded as an actual nonnegative
homogeneous Laurent weight of the same degree. -/
def projectiveMonomialPositiveWeight (l : ℕ) (b : ProjectiveMonomialIndex σ l) :
    HomogeneousLaurentExponent σ (l:ℤ) := by
  classical
  let e : σ →₀ ℤ := Finsupp.equivFunOnFinite.symm (fun i => (b.1 i : ℤ))
  refine ⟨e, ?_⟩
  rw [Finsupp.degree_eq_sum]
  change (∑ i : σ, (b.1 i : ℤ)) = (l:ℤ)
  exact_mod_cast (Finsupp.degree_eq_sum b.1).symm.trans b.property

theorem projectiveMonomialPositiveWeight_apply (l : ℕ) (b : ProjectiveMonomialIndex σ l) (i : σ) :
    (projectiveMonomialPositiveWeight l b).1 i = (b.1 i : ℤ) := rfl

theorem projectiveMonomialPositiveWeight_nonnegative (l : ℕ) (b : ProjectiveMonomialIndex σ l) :
    ∀ i, 0 ≤ (projectiveMonomialPositiveWeight l b).1 i := fun _ => Int.natCast_nonneg _

theorem projectiveMonomialPositiveWeight_natExponent (l : ℕ) (b : ProjectiveMonomialIndex σ l) :
    (projectiveMonomialPositiveWeight l b).natExponent = b.1 := by
  ext i
  simp [HomogeneousLaurentExponent.natExponent, projectiveMonomialPositiveWeight_apply]
end MvPolynomial
