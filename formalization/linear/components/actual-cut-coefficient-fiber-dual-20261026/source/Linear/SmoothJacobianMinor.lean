module
public import Linear.LocalizedDifferentialBasis
public import Linear.SplitJacobianRank
public import Linear.PolynomialPointEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped TensorProduct
namespace LinearStudy

def polynomialLocalCotangentSpaceBasis {K σ : Type*} [Field K]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] :
    Module.Basis σ
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))
      (polynomialLocalQuotientExtension I P).CotangentSpace :=
  (polynomialLocalizedDifferentialBasis P).baseChange
    (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))

theorem polynomialLocalCotangentSpaceBasis_repr_mk {K σ : Type*} [Field K]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (G : MvPolynomial σ K)
    (hG : algebraMap _ (Localization.AtPrime P) G ∈ (polynomialLocalQuotientExtension I P).ker)
    (i : σ) :
    (polynomialLocalCotangentSpaceBasis I P).repr
      ((polynomialLocalQuotientExtension I P).cotangentComplex
        (Algebra.Extension.Cotangent.mk ⟨algebraMap _ (Localization.AtPrime P) G, hG⟩)) i =
      Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime P)))
        (algebraMap _ (Localization.AtPrime P) (MvPolynomial.pderiv i G)) := by
  change ((polynomialLocalizedDifferentialBasis P).baseChange
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))).repr
    (1 ⊗ₜ[Localization.AtPrime P] KaehlerDifferential.D K (Localization.AtPrime P)
      (algebraMap (MvPolynomial σ K) (Localization.AtPrime P) G)) i = _
  exact polynomialLocalizedDifferentialBasis_baseChange_repr_D
    (Q := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))) P G i

theorem smooth_polynomial_jacobian_nonzero_minor {K σ : Type*} [Field K] [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))]
    (ρ : (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))) →ₐ[K] K)
    {n : ℕ} (G : Fin n → MvPolynomial σ K)
    (hG : ∀ i, algebraMap _ (Localization.AtPrime P) (G i) ∈
      (polynomialLocalQuotientExtension I P).ker)
    (b : Module.Basis (Fin n)
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))
      (polynomialLocalQuotientExtension I P).Cotangent)
    (hb : ∀ i, Algebra.Extension.Cotangent.mk
      ⟨algebraMap _ (Localization.AtPrime P) (G i), hG i⟩ = b i) :
    ∃ j : Fin n → σ, Function.Injective j ∧
      Matrix.det (fun i k => ρ
        (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime P)))
          (algebraMap _ (Localization.AtPrime P) (MvPolynomial.pderiv (j k) (G i))))) ≠ 0 := by
  let Q := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))
  let E := polynomialLocalQuotientExtension I P
  let : Algebra Q K := ρ.toAlgebra
  let : Algebra.FormallySmooth K E.Ring :=
    inferInstanceAs (Algebra.FormallySmooth K (Localization.AtPrime P))
  obtain ⟨l, hl⟩ := (Algebra.Extension.formallySmooth_iff_split_injection E).mp inferInstance
  obtain ⟨j, hj, hd⟩ := split_basis_residue_coordinates_nonzero_minor (K := K)
    b (polynomialLocalCotangentSpaceBasis I P) E.cotangentComplex l hl
  refine ⟨j, hj, ?_⟩
  change Matrix.det (fun (i k : Fin n) => ρ
    ((polynomialLocalCotangentSpaceBasis I P).repr (E.cotangentComplex (b i)) (j k))) ≠ 0 at hd
  have he : (fun (i k : Fin n) => ρ
      ((polynomialLocalCotangentSpaceBasis I P).repr (E.cotangentComplex (b i)) (j k))) =
      (fun (i k : Fin n) => ρ (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime P)))
        (algebraMap _ (Localization.AtPrime P) (MvPolynomial.pderiv (j k) (G i))))) := by
    funext i k
    rw [← hb i, polynomialLocalCotangentSpaceBasis_repr_mk]
  rwa [he] at hd

/-- From smoothness at an actual rational point, construct polynomial local
equations and a nonzero original-coordinate Jacobian minor. -/
theorem exists_smooth_polynomial_jacobian_generators_at_point
    {K σ : Type*} [Field K] [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P) (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))] :
    ∃ (n : ℕ) (G : Fin n → MvPolynomial σ K),
      I.map (algebraMap _ (Localization.AtPrime P)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))) ∧
      (∀ i, MvPolynomial.eval x (G i) = 0) ∧
      ∃ j : Fin n → σ, Function.Injective j ∧
        Matrix.det (fun i k => MvPolynomial.eval x (MvPolynomial.pderiv (j k) (G i))) ≠ 0 := by
  obtain ⟨n, G, hG, b, hb, hs⟩ := exists_smooth_polynomial_local_generators I P hIP
  let ρ := polynomialPointLocalQuotientEvaluation I P hIP x hP
  refine ⟨n, G, hs, ?_, ?_⟩
  · intro i
    have hi := hG i
    change Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime P)))
      (algebraMap _ (Localization.AtPrime P) (G i)) = 0 at hi
    rw [← polynomialPointLocalQuotientEvaluation_polynomial I P hIP x hP (G i), hi,
      map_zero]
  · obtain ⟨j, hj, hd⟩ := smooth_polynomial_jacobian_nonzero_minor I P ρ G hG b hb
    refine ⟨j, hj, ?_⟩
    simpa only [ρ, polynomialPointLocalQuotientEvaluation_polynomial] using hd

end LinearStudy
