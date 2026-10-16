module
public import Linear.CommonPolynomialCoordinates
public import Linear.SmoothFixedConormalRank
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open scoped Matrix

/-- Smoothness at finitely many actual rational points, with a common actual
conormal rank, constructs local polynomial equations and ONE common ambient
polynomial coordinate automorphism. Neither equations nor Jacobian rank are
assumed. Constancy of the conormal rank remains explicit. -/
theorem smooth_points_have_common_polynomial_coordinates {K σ ι : Type*}
    [Field K] [Infinite K] [Fintype σ] [DecidableEq σ] [Fintype ι]
    (I : Ideal (MvPolynomial σ K)) (P : ι → Ideal (MvPolynomial σ K))
    [∀ a, (P a).IsPrime] (x : ι → σ → K)
    (hIP : ∀ a, I ≤ P a)
    (hP : ∀ a, P a = RingHom.ker (MvPolynomial.aeval (R := K) (x a)).toRingHom)
    [∀ a, Algebra.FormallySmooth K
      (Localization.AtPrime (P a) ⧸ I.map (algebraMap _ (Localization.AtPrime (P a))))]
    {c : ℕ} (ν : Fin c → σ) (hν : Function.Injective ν)
    (hc : ∀ a, Module.finrank
      (Localization.AtPrime (P a) ⧸ I.map (algebraMap _ (Localization.AtPrime (P a))))
      (polynomialLocalQuotientExtension I (P a)).Cotangent = c) :
    ∃ (G : ι → Fin c → MvPolynomial σ K) (M : Matrix σ σ K) (hM : Matrix.det M ≠ 0),
      let e := polynomialLinearChangeEquiv M hM
      ∀ a,
        I.map (algebraMap _ (Localization.AtPrime (P a))) =
          Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime (P a)) (G a i))) ∧
        (∀ i, MvPolynomial.eval (x a) (G a i) = 0) ∧
        (∀ i, MvPolynomial.eval (M⁻¹ *ᵥ x a) (e (G a i)) = 0) ∧
        Matrix.det (fun i k => MvPolynomial.eval (M⁻¹ *ᵥ x a)
          (MvPolynomial.pderiv (ν k) (e (G a i)))) ≠ 0 := by
  choose G hs hz hLI using fun a =>
    exists_smooth_local_generators_of_conormal_rank I (P a) (hIP a) (x a) (hP a) c (hc a)
  obtain ⟨M, hM, h⟩ := exists_common_polynomial_normal_coordinates ν hν G x hLI
  refine ⟨G, M, hM, ?_⟩
  intro e a
  refine ⟨hs a, hz a, ?_, (h a).2⟩
  intro i
  rw [(h a).1 i, hz a i]

end LinearStudy
