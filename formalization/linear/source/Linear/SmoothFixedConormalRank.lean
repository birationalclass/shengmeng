module
public import Linear.SmoothJacobianMinor
public import Linear.SmoothCotangentDimension
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy

theorem smooth_polynomial_jacobian_rows_linearIndependent
    {K σ : Type*} [Field K] [Finite σ]
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
    LinearIndependent K (fun i j => ρ
      (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime P)))
        (algebraMap _ (Localization.AtPrime P) (MvPolynomial.pderiv j (G i))))) := by
  let Q := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))
  let E := polynomialLocalQuotientExtension I P
  let : Algebra Q K := ρ.toAlgebra
  let : Algebra.FormallySmooth K E.Ring :=
    inferInstanceAs (Algebra.FormallySmooth K (Localization.AtPrime P))
  obtain ⟨l, hl⟩ := (Algebra.Extension.formallySmooth_iff_split_injection E).mp inferInstance
  have h := split_basis_residue_coordinates_linearIndependent (K := K)
    b (polynomialLocalCotangentSpaceBasis I P) E.cotangentComplex l hl
  change LinearIndependent K (fun i j => ρ
    ((polynomialLocalCotangentSpaceBasis I P).repr (E.cotangentComplex (b i)) j)) at h
  have he : (fun (i : Fin n) (j : σ) => ρ
      ((polynomialLocalCotangentSpaceBasis I P).repr (E.cotangentComplex (b i)) j)) =
      (fun (i : Fin n) (j : σ) => ρ (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime P)))
        (algebraMap _ (Localization.AtPrime P) (MvPolynomial.pderiv j (G i))))) := by
    funext i j
    rw [← hb i, polynomialLocalCotangentSpaceBasis_repr_mk]
  rwa [he] at h

/-- For a prescribed actual conormal rank, smoothness constructs that many
polynomial local generators and their independent derivative rows. -/
theorem exists_smooth_local_generators_of_conormal_rank
    {K σ : Type*} [Field K] [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P) (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))]
    (c : ℕ) (hc : Module.finrank
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))
      (polynomialLocalQuotientExtension I P).Cotangent = c) :
    ∃ G : Fin c → MvPolynomial σ K,
      I.map (algebraMap _ (Localization.AtPrime P)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))) ∧
      (∀ i, MvPolynomial.eval x (G i) = 0) ∧
      LinearIndependent K (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (G i))) := by
  obtain ⟨n, G, hG, b, hb, hs⟩ := exists_smooth_polynomial_local_generators I P hIP
  let Q := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr (polynomial_local_ideal_ne_top I P hIP)
  have hn : n = c := by
    have h := Module.finrank_eq_card_basis b
    simp only [Fintype.card_fin] at h
    exact h.symm.trans hc
  subst n
  let ρ := polynomialPointLocalQuotientEvaluation I P hIP x hP
  refine ⟨G, hs, ?_, ?_⟩
  · intro i
    have hi := hG i
    change Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime P)))
      (algebraMap _ (Localization.AtPrime P) (G i)) = 0 at hi
    rw [← polynomialPointLocalQuotientEvaluation_polynomial I P hIP x hP (G i), hi, map_zero]
  · have h := smooth_polynomial_jacobian_rows_linearIndependent I P ρ G hG b hb
    simpa only [ρ, polynomialPointLocalQuotientEvaluation_polynomial] using h

end LinearStudy
