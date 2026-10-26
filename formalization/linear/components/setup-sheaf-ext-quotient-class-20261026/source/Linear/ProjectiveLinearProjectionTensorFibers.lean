module
public import Linear.FiniteProjectionTensorFibers
public import Mathlib.Algebra.MvPolynomial.Funext
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open scoped TensorProduct
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual generic scalar fibers of the original linear normalization.
Both the linear map and a nonempty target open away from the zero-th
coordinate are constructed; no reduced fiber or point count is assumed.
Projective point/section comparison and degree V remain separate bridges. -/
theorem projective_exists_linear_projection_reduced_rank_fibers {n : ℕ}
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
        let R := MvPolynomial (Fin (r+1)) ℂ
        let A := CoordinateRing n ⧸ V.ideal.toIdeal
        let φ := projectiveLinearNormalizationMap V L
        letI : Algebra R A := φ.toRingHom.toAlgebra
        letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
        letI : Module R A := Algebra.toModule
        ∃ c : R, c ≠ 0 ∧
          (∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
          ∀ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
            w 0 ≠ 0 ∧
            letI : Algebra R ℂ := (MvPolynomial.aeval w).toRingHom.toAlgebra
            Module.Finite ℂ (ℂ ⊗[R] A) ∧ IsReduced (ℂ ⊗[R] A) ∧
              Module.finrank ℂ (ℂ ⊗[R] A) = Module.finrank R A ∧
              Nat.card ((ℂ ⊗[R] A) →ₐ[ℂ] ℂ) = Module.finrank R A := by
  classical
  letI := V.prime
  obtain ⟨r,P,hr,hP,hdeg,hHilbert,L,hL,hinj,hfinite,_,hfree⟩ :=
    projective_exists_linear_normalization V
  refine ⟨r,P,hr,hP,hdeg,hHilbert,L,hL,hinj,hfinite,hfree,?_⟩
  let R := MvPolynomial (Fin (r+1)) ℂ
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
  letI : Module R A := Algebra.toModule
  letI : Algebra.FinitePresentation ℂ R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra.FinitePresentation ℂ A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨c,hc,hfib⟩ := finite_injective_algHom_exists_reduced_rank_fibers φ hinj hfinite
  let c' : R := c * MvPolynomial.X 0
  have hc' : c' ≠ 0 := mul_ne_zero hc (MvPolynomial.X_ne_zero 0)
  have hex : ∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c' ≠ 0 := by
    by_contra h
    push Not at h
    apply hc'
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    exact h w
  refine ⟨c',hc',hex,?_⟩
  intro w hw
  change MvPolynomial.eval w (c * MvPolynomial.X 0) ≠ 0 at hw
  rw [MvPolynomial.eval_mul,MvPolynomial.eval_X] at hw
  have he : MvPolynomial.eval w c ≠ 0 ∧ w 0 ≠ 0 :=
    mul_ne_zero_iff.mp hw
  exact ⟨he.2,hfib (MvPolynomial.aeval w) he.1⟩

end LinearStudy
