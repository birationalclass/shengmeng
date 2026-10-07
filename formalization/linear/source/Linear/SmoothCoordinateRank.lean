module
public import Linear.LocalizedDifferentialRank
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
attribute [local instance] polynomialLocalDifferentialModule

/-- Retain the actual differential rank of the constructed tangent coordinates,
so their number is not merely some finite number of ideal generators. -/
theorem smooth_generators_coordinate_split_with_rank
    {K σ : Type*} [Field K] [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P) (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))] :
    ∃ (r c : ℕ) (e : (Fin r ⊕ Fin c) ≃ σ) (G : Fin c → MvPolynomial σ K),
      r = Module.finrank (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))
        (KaehlerDifferential K
          (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))) ∧
      I.map (algebraMap _ (Localization.AtPrime P)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))) ∧
      (∀ i, MvPolynomial.eval (x ∘ e) (MvPolynomial.rename e.symm (G i)) = 0) ∧
      IsUnit (Matrix.det (fun i j => MvPolynomial.eval (x ∘ e)
        (MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.rename e.symm (G i))))) := by
  let Q := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr (polynomial_local_ideal_ne_top I P hIP)
  obtain ⟨c, G, hG, b, hb, hs⟩ := exists_smooth_polynomial_local_generators I P hIP
  have hn : Module.finrank Q (polynomialLocalQuotientExtension I P).Cotangent = c := by
    simpa using Module.finrank_eq_card_basis b
  let ρ := polynomialPointLocalQuotientEvaluation I P hIP x hP
  obtain ⟨j, hj, hd⟩ := smooth_polynomial_jacobian_nonzero_minor I P ρ G hG b hb
  obtain ⟨r, e, he⟩ := exists_coordinate_split j hj
  have hnum : r + c = Nat.card σ := by
    simpa only [Nat.card_sum, Nat.card_fin] using Nat.card_congr e
  have hsum := smooth_polynomial_cotangent_finrank_add I P hIP
  change Module.finrank Q (polynomialLocalQuotientExtension I P).Cotangent +
    Module.finrank Q (KaehlerDifferential K Q) = Nat.card σ at hsum
  rw [hn] at hsum
  refine ⟨r, c, e, G, ?_, hs, ?_, ?_⟩
  · change r = Module.finrank Q (KaehlerDifferential K Q)
    omega
  · intro i
    rw [polynomial_eval_coordinate_equiv]
    have hi := hG i
    change Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime P)))
      (algebraMap _ (Localization.AtPrime P) (G i)) = 0 at hi
    rw [← polynomialPointLocalQuotientEvaluation_polynomial I P hIP x hP (G i), hi, map_zero]
  · apply isUnit_iff_ne_zero.mpr
    have hm : (fun i k => MvPolynomial.eval (x ∘ e)
        (MvPolynomial.pderiv (Sum.inr k) (MvPolynomial.rename e.symm (G i)))) =
        (fun i k => MvPolynomial.eval x (MvPolynomial.pderiv (j k) (G i))) := by
      funext i k
      rw [polynomial_derivative_eval_coordinate_equiv, he]
    rw [hm]
    simpa only [ρ, polynomialPointLocalQuotientEvaluation_polynomial] using hd
end LinearStudy
