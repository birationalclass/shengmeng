module
public import Linear.OriginalProjectivePolynomialSurjective
public import Linear.OriginalPolynomialEmbeddingNonzero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ORIGINAL polynomial extension/nonzero step with a proved lift.
The bound depends only on V and precedes every degree, embedding and
nonzero section. The monomorphism and nonzero section remain their actual
geometric inputs; this does NOT prove their original4.1/Koszul existence.
No polynomial lifting or lifting equality is supplied as an assumption. -/
theorem originalProjectivePolynomial_eventually_nonzero_after_mono {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let B := homogeneousQuotientPiece V.ideal.toIdeal
    let T := fun N : ℕ => nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
      (nativeProjectiveRingIntegerPiece_graded B) (N : ℤ)
    ∃ n₀ : ℕ, ∀ N : ℕ, n₀ ≤ N →
      ∀ (F : (Proj B).Modules) (j : F ⟶ T N), Mono j →
      ∀ s : Γ(F,⊤), s ≠ 0 →
      ∃ Q : CoordinateRing n, ∃ hQ : Q.IsHomogeneous N,
        originalProjectivePolynomialSection V N Q hQ = j.app ⊤ s ∧ Q ∉ V.ideal.toIdeal := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  obtain ⟨n₀,hn₀⟩ := originalProjectivePolynomial_eventually_sections_lift V
  refine ⟨n₀,fun N hN F j hj s hs => ?_⟩
  obtain ⟨Q,hQ,hLift⟩ := hn₀ N hN (j.app ⊤ s)
  exact ⟨Q,hQ,hLift,originalProjectivePolynomial_lift_after_mono_not_mem
    V N Q hQ F j hj s hs hLift⟩
end LinearStudy
