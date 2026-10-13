module
public import Linear.LaurentMonomialBasis
@[expose] public section
noncomputable section
namespace MvPolynomial
variable (R : Type) [CommRing R] {σ : Type}

/-- Actual multiplication by a polynomial in a monomial localization agrees
with multiplication of its Laurent coordinates. -/
theorem laurent_actual_polynomial_multiplication (m : σ →₀ ℕ)
    (p : MvPolynomial σ R) (x : Localization.Away (monomial m (1 : R))) :
    laurentMonomialRingEquiv R m
      (algebraMap (MvPolynomial σ R) (Localization.Away (monomial m (1 : R))) p * x) =
    AddMonoidAlgebra.mapDomain (laurentExponentAwayMap m).toAddMonoidHom p *
      laurentMonomialRingEquiv R m x := by
  rw [map_mul, laurentMonomialRingEquiv_algebraMap]

/-- Actual monomial multiplication shifts a Laurent basis exponent.
This is a chart-local identity, not yet a native sheaf comparison. -/
theorem laurent_actual_monomial_basis_multiplication (m b : σ →₀ ℕ)
    (e : laurentExponentSubmonoid m) :
    algebraMap (MvPolynomial σ R) (Localization.Away (monomial m (1 : R)))
      (monomial b 1) * laurentMonomialBasis R m e =
    laurentMonomialBasis R m ((laurentExponentAwayMap m) b + e) := by
  apply (laurentMonomialRingEquiv R m).injective
  rw [laurent_actual_polynomial_multiplication, laurentMonomialRingEquiv_basis_apply,
    laurentMonomialRingEquiv_basis_apply]
  change AddMonoidAlgebra.mapDomain (laurentExponentAwayMap m).toAddMonoidHom
    (AddMonoidAlgebra.single b 1) * AddMonoidAlgebra.single e 1 = _
  rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single, one_mul]
  rfl
end MvPolynomial
