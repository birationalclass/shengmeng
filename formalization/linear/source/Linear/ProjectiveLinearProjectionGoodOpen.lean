module
public import Linear.FiniteLinearProjectionGoodOpen
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Construct the same original basepoint-free linear normalization and
a good target open whose ENTIRE cone preimage is smooth, unramified
and avoids any chosen nonzero source element. Generic section degree
and simultaneous projective target selection are not yet asserted. -/
theorem projective_exists_linear_projection_target_good_loci {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    letI := V.prime
    ∃ (r : ℕ) (P : Polynomial ℚ), r ≤ n ∧ P ≠ 0 ∧ P.natDegree = r ∧
      (∃ N : ℕ, ∀ m > N, P.eval (m : ℚ) =
        (homogeneousQuotientHilbert V.ideal.toIdeal m : ℚ)) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i, (L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        (∀ (v : CoordinateVector n), v ≠ 0 →
          (∀ H ∈ V.ideal.toIdeal, MvPolynomial.eval v H = 0) →
          (fun i => MvPolynomial.eval v (L i)) ≠ 0) ∧
        ∀ (a : CoordinateRing n ⧸ V.ideal.toIdeal), a ≠ 0 →
          let φ := projectiveLinearNormalizationMap V L
          letI : Algebra (MvPolynomial (Fin (r+1)) ℂ)
            (CoordinateRing n ⧸ V.ideal.toIdeal) := φ.toRingHom.toAlgebra
          ∃ c : MvPolynomial (Fin (r+1)) ℂ, c ≠ 0 ∧ φ c ≠ 0 ∧
            ∀ Q : PrimeSpectrum (CoordinateRing n ⧸ V.ideal.toIdeal),
              φ c ∉ Q.asIdeal → a ∉ Q.asIdeal ∧
                Q ∈ Algebra.smoothLocus ℂ (CoordinateRing n ⧸ V.ideal.toIdeal) ∧
                PrimeSpectrum.comap φ.toRingHom Q ∈
                  Algebra.smoothLocus ℂ (MvPolynomial (Fin (r+1)) ℂ) ∧
                Q ∈ Algebra.unramifiedLocus (MvPolynomial (Fin (r+1)) ℂ)
                  (CoordinateRing n ⧸ V.ideal.toIdeal) := by
  letI := V.prime
  obtain ⟨r,P,hr,hP,hdeg,hHilbert,L,hL,hinj,hfinite,_,hfree⟩ :=
    projective_exists_linear_normalization V
  refine ⟨r,P,hr,hP,hdeg,hHilbert,L,hL,hinj,hfinite,hfree,?_⟩
  intro a ha
  let R := MvPolynomial (Fin (r+1)) ℂ
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  letI : Algebra.FinitePresentation ℂ R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra.FinitePresentation ℂ A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact finite_injective_algHom_exists_target_good_loci_avoiding
    (projectiveLinearNormalizationMap V L) hinj hfinite a ha

end LinearStudy
