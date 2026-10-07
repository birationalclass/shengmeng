module
public import Linear.PolynomialNormalEquations
public import Linear.LocalGeneratorsEquiv
public import Linear.SmoothTargetFirstOrder
public import Linear.PolynomialLocalParameters
public import Linear.SmoothCoordinateRank
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open scoped Matrix
attribute [local instance] polynomialLocalDifferentialModule

/-- Normalize actual polynomial generators of the ORIGINAL localized ideal.
No ideal image in a completed ring substitutes for the actual local ideal. -/
theorem original_local_ideal_normal_polynomial_generators
    {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (I : Ideal (MvPolynomial (α ⊕ β) K)) (x : α ⊕ β → K)
    (G : β → MvPolynomial (α ⊕ β) K)
    (hs : letI : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime :=
        RingHom.ker_isPrime _
      I.map (algebraMap _ (Localization.AtPrime
          (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom))) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime
          (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)) (G i))))
    (h0 : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    ∃ (M : Matrix (α ⊕ β) (α ⊕ β) K) (hM : Matrix.det M ≠ 0)
      (H : β → MvPolynomial (α ⊕ β) K),
      (∀ i, MvPolynomial.eval (M⁻¹ *ᵥ x) (H i) = 0) ∧
      (∀ i j, MvPolynomial.eval (M⁻¹ *ᵥ x) (MvPolynomial.pderiv j (H i)) =
        if j = Sum.inr i then 1 else 0) ∧
      let Q := RingHom.ker (MvPolynomial.aeval (R := K) (M⁻¹ *ᵥ x)).toRingHom
      letI : Q.IsPrime := RingHom.ker_isPrime _
      (I.map (polynomialLinearChangeEquiv M hM).toRingHom).map
        (algebraMap _ (Localization.AtPrime Q)) =
          Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i))) := by
  classical
  obtain ⟨M, hM, H, h0H, hDH, hideal⟩ := polynomial_equations_adapted_normal_generators G x h0 hJ
  refine ⟨M, hM, H, h0H, hDH, ?_⟩
  let Q := RingHom.ker (MvPolynomial.aeval (R := K) (M⁻¹ *ᵥ x)).toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime _
  have hs' := polynomial_local_generators_under_linear_change I x M hM G hs
  have hh := congrArg (fun J : Ideal (MvPolynomial (α ⊕ β) K) =>
    J.map (algebraMap _ (Localization.AtPrime Q))) hideal
  rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp] at hh
  exact hs'.trans hh.symm

/-- Actual smoothness constructs the normal polynomial equations used by
the actual point-local parameter lemma. -/
theorem smooth_point_original_ideal_normal_polynomial_generators
    {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P) (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (hI : I.map (algebraMap _ (Localization.AtPrime P)) ≠ ⊥)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))] :
    ∃ (r c : ℕ) (hc : 0 < c)
      (e : (Fin r ⊕ Fin c) ≃ σ)
      (M : Matrix (Fin r ⊕ Fin c) (Fin r ⊕ Fin c) K) (hM : Matrix.det M ≠ 0)
      (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) K),
      r = Module.finrank (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))
        (KaehlerDifferential K
          (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))) ∧
      (∀ i, MvPolynomial.eval (M⁻¹ *ᵥ (x ∘ e)) (H i) = 0) ∧
      (∀ i j, MvPolynomial.eval (M⁻¹ *ᵥ (x ∘ e)) (MvPolynomial.pderiv j (H i)) =
        if j = Sum.inr i then 1 else 0) ∧
      let Q := RingHom.ker (MvPolynomial.aeval (R := K) (M⁻¹ *ᵥ (x ∘ e))).toRingHom
      letI : Q.IsPrime := RingHom.ker_isPrime _
      (I.map ((polynomialLinearChangeEquiv M hM).toRingHom.comp
        (MvPolynomial.rename e.symm).toRingHom)).map
        (algebraMap _ (Localization.AtPrime Q)) =
          Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i))) := by
  classical
  obtain ⟨r, c, e, G, hr, hs, h0, hJ⟩ :=
    smooth_generators_coordinate_split_with_rank I P hIP x hP
  have hc : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro hc
    subst c
    apply hI
    simpa using hs
  let E := MvPolynomial.renameEquiv K e.symm
  let y := x ∘ e
  let Q := RingHom.ker (MvPolynomial.aeval (R := K) y).toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime _
  have hPQ : P = Q.comap E.toRingHom := by
    rw [hP]
    ext F
    change MvPolynomial.eval x F = 0 ↔ MvPolynomial.eval (x ∘ e) (MvPolynomial.rename e.symm F) = 0
    rw [polynomial_eval_coordinate_equiv]
  have hsE := local_ideal_generators_under_ringEquiv I P Q E.toRingEquiv hPQ G hs
  obtain ⟨M, hM, H, h0H, hDH, hideal⟩ := original_local_ideal_normal_polynomial_generators
    (I.map E.toRingHom) y (fun i => E (G i)) hsE h0 hJ
  refine ⟨r, c, hc, e, M, hM, H, hr, h0H, hDH, ?_⟩
  rw [Ideal.map_map] at hideal
  exact hideal
end LinearStudy
