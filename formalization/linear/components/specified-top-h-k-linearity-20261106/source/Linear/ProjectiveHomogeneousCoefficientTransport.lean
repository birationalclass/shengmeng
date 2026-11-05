module
public import Linear.ProjectiveHomogeneousBasisProduct
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
variable {R S : Type} [CommRing R] [CommRing S] {σ : Type}

/-- Restrict mathlib's ACTUAL polynomial coefficient map to homogeneous
pieces. It is semilinear over the original coefficient-ring map. -/
def projectiveHomogeneousCoefficientMap (φ : R →+* S) (m : ℕ) :
    homogeneousSubmodule σ R m →ₛₗ[φ] homogeneousSubmodule σ S m where
  toFun p := ⟨MvPolynomial.map φ p.1, p.property.map φ⟩
  map_add' p q := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r p := by
    apply Subtype.ext
    change MvPolynomial.map φ (r • p.1) = φ r • MvPolynomial.map φ p.1
    rw [smul_eq_C_mul, map_mul, map_C, smul_eq_C_mul]

variable [Fintype σ] [LinearOrder σ]

theorem projectiveHomogeneousCoefficientMap_basis (φ : R →+* S) (m : ℕ)
    (b : ProjectiveMonomialIndex σ m) :
    projectiveHomogeneousCoefficientMap φ m (projectiveHomogeneousMonomialBasis (R := R) m b) =
      projectiveHomogeneousMonomialBasis (R := S) m b := by
  apply Subtype.ext
  change MvPolynomial.map φ (projectiveHomogeneousMonomialBasis (R := R) m b).1 =
    (projectiveHomogeneousMonomialBasis (R := S) m b).1
  rw [projectiveHomogeneousMonomialBasis_coe, projectiveHomogeneousMonomialBasis_coe,
    map_monomial, map_one]

theorem projectiveHomogeneousCoefficientMap_scaled_basis (φ : R →+* S) (m : ℕ)
    (b : ProjectiveMonomialIndex σ m) (r : R) :
    projectiveHomogeneousCoefficientMap φ m (r • projectiveHomogeneousMonomialBasis (R := R) m b) =
      φ r • projectiveHomogeneousMonomialBasis (R := S) m b := by
  rw [map_smulₛₗ, projectiveHomogeneousCoefficientMap_basis]

/-- A scaled basis vector is the original monomial with its original coefficient. -/
theorem projectiveHomogeneousMonomialBasis_scaled_coe (m : ℕ)
    (b : ProjectiveMonomialIndex σ m) (r : R) :
    (r • projectiveHomogeneousMonomialBasis (R := R) m b).1 = monomial b.1 r := by
  change r • (projectiveHomogeneousMonomialBasis (R := R) m b).1 = _
  rw [projectiveHomogeneousMonomialBasis_coe, smul_monomial, smul_eq_mul, mul_one]

end MvPolynomial
