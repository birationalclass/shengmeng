module
public import Linear.ProjectiveLaurentZeroCycle
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
universe u
variable {σ : Type} [Fintype σ]

/-- The natural exponent vector of a Laurent weight. The comparison
theorems below explicitly require that all original exponents be nonnegative. -/
def HomogeneousLaurentExponent.natExponent {d : ℤ}
    (e : HomogeneousLaurentExponent σ d) : σ →₀ ℕ :=
  e.1.mapRange Int.toNat (by rfl)

/-- Casting the natural exponent vector recovers every original Laurent
exponent once chart compatibility has excluded negative terms. -/
theorem HomogeneousLaurentExponent.natExponent_cast_apply {d : ℤ}
    (e : HomogeneousLaurentExponent σ d) (he : ∀ i, 0 ≤ e.1 i) (i : σ) :
    ((e.natExponent i : ℕ) : ℤ) = e.1 i := by
  simp only [natExponent,Finsupp.mapRange_apply,Int.toNat_of_nonneg (he i)]

/-- The monomial assembled from a nonnegative degree-m Laurent weight
has EXACTLY the original homogeneous degree m. -/
theorem HomogeneousLaurentExponent.natExponent_degree (m : ℕ)
    (e : HomogeneousLaurentExponent σ (m : ℤ)) (he : ∀ i, 0 ≤ e.1 i) :
    e.natExponent.degree = m := by
  apply Int.natCast_inj.mp
  rw [Finsupp.degree_eq_sum,Nat.cast_sum]
  simp_rw [e.natExponent_cast_apply he]
  exact (Finsupp.degree_eq_sum e.1).symm.trans e.property

/-- Nonnegative Laurent weights therefore supply actual homogeneous
polynomials, over the original coefficient field or ring. -/
theorem HomogeneousLaurentExponent.natExponent_monomial_homogeneous
    {R : Type u} [CommRing R] (m : ℕ)
    (e : HomogeneousLaurentExponent σ (m : ℤ)) (he : ∀ i, 0 ≤ e.1 i) (c : R) :
    (monomial e.natExponent c).IsHomogeneous m :=
  isHomogeneous_monomial c (e.natExponent_degree m he)
end MvPolynomial
