module
public import Linear.NativePrimeQuotientPolynomialSections
public import Linear.OriginalProjectivePolynomialSection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra

/-- For the ORIGINAL integral complex projective equations, one bound
depending only on V's actual ideal precedes ALL degrees and ALL actual
twist sections. The lift uses the ORIGINAL polynomial ring and ORIGINAL
polynomial-section map; no global lifting equality is an assumption. -/
theorem originalProjectivePolynomial_eventually_sections_lift {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let B := homogeneousQuotientPiece V.ideal.toIdeal
    ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N →
      ∀ s : Γ(nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
        (nativeProjectiveRingIntegerPiece_graded B) (N : ℤ),⊤),
      ∃ Q : CoordinateRing n, ∃ hQ : Q.IsHomogeneous N,
        originalProjectivePolynomialSection V N Q hQ = s := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : V.ideal.toIdeal.IsPrime := V.prime
  obtain ⟨n₀,hn₀⟩ := homogeneousPrimeQuotient_eventually_actual_polynomial_sections
    V.ideal.toIdeal V.ideal.isHomogeneous (0 : Fin (n+1))
  refine ⟨n₀,fun N hN s => ?_⟩
  obtain ⟨Q,hQ⟩ := hn₀ N hN s
  refine ⟨Q,Q.property,?_⟩
  have he : originalProjectivePolynomialSection V N (Q : CoordinateRing n) Q.property =
      quotientProjHomogeneousPolynomialSection V.ideal.toIdeal V.ideal.isHomogeneous N Q := by
    apply Subtype.ext
    rfl
  exact he.trans hQ
end LinearStudy
