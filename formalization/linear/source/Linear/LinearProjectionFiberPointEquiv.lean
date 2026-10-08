module
public import Linear.ProjectiveLinearProjectionTensorFibers
public import Linear.PolynomialReducedPointCount
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open scoped TensorProduct
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Compatible scalar evaluations of A are exactly algebra maps over
the actual target evaluation. No point-count formula is an input. -/
def compatibleScalarPointEquiv
    {K R A : Type*} [Field K] [CommRing R] [CommRing A]
    [Algebra K R] [Algebra K A]
    (φ : R →ₐ[K] A) (ρ : R →ₐ[K] K) :
    letI : Algebra R A := φ.toRingHom.toAlgebra
    letI : Algebra R K := ρ.toRingHom.toAlgebra
    {ψ : A →ₐ[K] K // ψ.comp φ = ρ} ≃ (A →ₐ[R] K) := by
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : Algebra R K := ρ.toRingHom.toAlgebra
  refine {
    toFun := fun ψ => { ψ.1.toRingHom with
      commutes' := fun r => AlgHom.congr_fun ψ.2 r }
    invFun := fun ψ => ?_
    left_inv := ?_
    right_inv := ?_ }
  · let χ : A →ₐ[K] K := { ψ.toRingHom with
      commutes' := fun k => by
        have h := ψ.commutes (algebraMap K R k)
        change ψ (φ (algebraMap K R k)) = ρ (algebraMap K R k) at h
        rw [φ.commutes,ρ.commutes] at h
        exact h }
    refine ⟨χ,?_⟩
    apply AlgHom.ext
    intro r
    exact ψ.commutes r
  · intro ψ
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    rfl
  · intro ψ
    apply AlgHom.ext
    intro a
    rfl

/-- The tensor-product fiber has exactly the compatible scalar points
of the original source algebra, by actual base-change universal property. -/
def tensorFiberScalarPointEquiv
    {K R A : Type*} [Field K] [CommRing R] [CommRing A]
    [Algebra K R] [Algebra K A]
    (φ : R →ₐ[K] A) (ρ : R →ₐ[K] K) :
    letI : Algebra R A := φ.toRingHom.toAlgebra
    letI : Algebra R K := ρ.toRingHom.toAlgebra
    {ψ : A →ₐ[K] K // ψ.comp φ = ρ} ≃ ((K ⊗[R] A) →ₐ[K] K) := by
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : Algebra R K := ρ.toRingHom.toAlgebra
  letI : IsScalarTower R K K := IsScalarTower.of_algebraMap_eq fun r => rfl
  exact (compatibleScalarPointEquiv φ ρ).trans (AlgHom.liftEquiv R K A K)

/-- Actual polynomial evaluations in the original cone fiber are
equivalent to its compatible source scalar maps. -/
def polynomialProjectionFiberPointEquiv
    {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (L : τ → MvPolynomial σ K) (w : τ → K) :
    {v : MvPolynomial.zeroLocus K I //
      (fun i => MvPolynomial.eval v.1 (L i)) = w} ≃
    {ψ : (MvPolynomial σ K ⧸ I) →ₐ[K] K //
      ψ.comp ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)) = MvPolynomial.aeval w} := by
  refine (polynomialZeroLocusPointEquiv I).subtypeEquiv ?_
  intro v
  constructor
  · intro h
    apply MvPolynomial.algHom_ext
    intro i
    simpa [polynomialZeroLocusPointEquiv,AlgHom.comp_apply,
      MvPolynomial.aeval_eq_eval] using congrFun h i
  · intro h
    funext i
    have hi := AlgHom.congr_fun h (MvPolynomial.X i)
    simpa [polynomialZeroLocusPointEquiv,AlgHom.comp_apply,
      MvPolynomial.aeval_eq_eval] using hi

/-- The ACTUAL original polynomial fiber, not a supplied abstract set,
has the same points as the ACTUAL tensor-product fiber. -/
def polynomialProjectionTensorPointEquiv
    {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (L : τ → MvPolynomial σ K) (w : τ → K) :
    let R := MvPolynomial τ K
    let A := MvPolynomial σ K ⧸ I
    let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
    letI : Algebra R A := φ.toRingHom.toAlgebra
    letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
    letI : Module R A := Algebra.toModule
    letI : Algebra R K := (MvPolynomial.aeval w).toRingHom.toAlgebra
    letI : SMul R K := (MvPolynomial.aeval w).toRingHom.toAlgebra.toSMul
    letI : Module R K := Algebra.toModule
    {v : MvPolynomial.zeroLocus K I //
      (fun i => MvPolynomial.eval v.1 (L i)) = w} ≃ ((K ⊗[R] A) →ₐ[K] K) := by
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
  letI : Module R A := Algebra.toModule
  letI : Algebra R K := (MvPolynomial.aeval w).toRingHom.toAlgebra
  letI : SMul R K := (MvPolynomial.aeval w).toRingHom.toAlgebra.toSMul
  letI : Module R K := Algebra.toModule
  exact (polynomialProjectionFiberPointEquiv I L w).trans
    (tensorFiberScalarPointEquiv φ (MvPolynomial.aeval w))

/-- The original V's ACTUAL coordinate fiber on the constructed good
target open has exactly the original finite linear projection's generic
rank. The point set is not supplied, and its cardinality is derived. -/
theorem projective_exists_linear_projection_cone_fiber_card {n : ℕ}
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
            w 0 ≠ 0 ∧ Nat.card {v : MvPolynomial.zeroLocus ℂ V.ideal.toIdeal //
              (fun i => MvPolynomial.eval v.1 (L i)) = w} = Module.finrank R A := by
  classical
  letI := V.prime
  obtain ⟨r,P,hr,hP,hdegree,hHilbert,L,hL,hinj,hfinite,hfree,c,hc,hex,hfib⟩ :=
    projective_exists_linear_projection_reduced_rank_fibers V
  refine ⟨r,P,hr,hP,hdegree,hHilbert,L,hL,hinj,hfinite,hfree,c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,_,_,_,hcard⟩ := hfib w hw
  refine ⟨hw0,?_⟩
  exact (Nat.card_congr (polynomialProjectionTensorPointEquiv V.ideal.toIdeal L w)).trans hcard

end LinearStudy
