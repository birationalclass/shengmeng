module
public import Linear.FiniteNormalizationFilteredBound
public import Linear.HomogeneousCoordinateFiltration
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- ACTUAL finite normalization gives an upper polynomial bound for the
ORIGINAL coordinate quotient filtration. Matrices and coefficient bounds
are constructed in the preceding theorem, not supplied in this statement. -/
theorem quotient_normalization_filtration_upper
    {k σ τ : Type*} [Field k] [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial τ k →ₐ[k] (MvPolynomial σ k ⧸ I)) (hg : g.Finite) :
    ∃ m c B : ℕ, 0 < c ∧ ∀ N : ℕ,
      Module.finrank k (homogeneousQuotientFiltration I N) ≤
        m * (c * N + B + 1) ^ Nat.card τ := by
  obtain ⟨m, b, c, B, hc, hbound⟩ := finite_normalization_polynomial_filtered_bound
    g hg (Ideal.Quotient.mkₐ k I)
  refine ⟨m, c, B, hc, ?_⟩
  intro N
  have hle : homogeneousQuotientFiltration I N ≤ boundedPolynomialSpan g b (c * N + B) := by
    intro a ha
    obtain ⟨H, hH, rfl⟩ := (homogeneousQuotientFiltration_mem_iff I N a).mp ha
    exact boundedPolynomialSpan_mono g b
      (Nat.add_le_add_right (Nat.mul_le_mul_left c hH) B) (hbound H)
  letI := boundedPolynomialSpan_finite g b (c * N + B)
  exact (Submodule.finrank_mono hle).trans (boundedPolynomialSpan_finrank_le g b (c * N + B))

end LinearStudy
