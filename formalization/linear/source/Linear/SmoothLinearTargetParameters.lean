module
public import Linear.SmoothTargetParameters
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open scoped Matrix
attribute [local instance] polynomialLocalDifferentialModule

/-- Strengthen the existing smooth-point construction by proving that its
actual original polynomial parameters are centered linear polynomials. -/
theorem smooth_point_constructs_original_linear_parameters
    {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P) (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (hI : I.map (algebraMap _ (Localization.AtPrime P)) ≠ ⊥)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))] :
    let J := I.map (algebraMap _ (Localization.AtPrime P))
    letI : Nontrivial (Localization.AtPrime P ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
      (polynomial_local_ideal_ne_top I P hIP)
    letI : IsLocalRing (Localization.AtPrime P ⧸ J) := IsLocalRing.of_surjective'
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    ∃ (r : ℕ) (a : Fin r → MvPolynomial σ K),
      r = Module.finrank (Localization.AtPrime P ⧸ J)
        (KaehlerDifferential K (Localization.AtPrime P ⧸ J)) ∧
      (∀ i, (a i).totalDegree ≤ 1 ∧ MvPolynomial.eval x (a i) = 0) ∧
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk J
        (algebraMap _ (Localization.AtPrime P) (a i)))) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P ⧸ J) := by
  classical
  let J := I.map (algebraMap _ (Localization.AtPrime P))
  letI : Nontrivial (Localization.AtPrime P ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top I P hIP)
  letI : IsLocalRing (Localization.AtPrime P ⧸ J) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  obtain ⟨r, c, hc, e, M, hM, H, hr, h0H, hDH, hlocal⟩ :=
    smooth_point_original_ideal_normal_polynomial_generators I P hIP x hP hI
  let C := (MvPolynomial.renameEquiv K e.symm).toRingEquiv.trans
    (polynomialLinearChangeEquiv M hM).toRingEquiv
  let y := M⁻¹ *ᵥ (x ∘ e)
  let Q := RingHom.ker (MvPolynomial.aeval (R := K) y).toRingHom
  letI : Q.IsPrime := RingHom.ker_isPrime _
  have hxy : M *ᵥ y = x ∘ e := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
  have hPQ : P = Q.comap C.toRingHom := by
    rw [hP]
    ext F
    change MvPolynomial.eval x F = 0 ↔ MvPolynomial.eval y
      (polynomialLinearChange M (MvPolynomial.rename e.symm F)) = 0
    rw [eval_polynomialLinearChange, hxy, polynomial_eval_coordinate_equiv]
  let I' := I.map C.toRingHom
  have hIQ : I' ≤ Q := Ideal.map_le_iff_le_comap.mpr (by rw [← hPQ]; exact hIP)
  let J' := I'.map (algebraMap _ (Localization.AtPrime Q))
  letI : Nontrivial (Localization.AtPrime Q ⧸ J') := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top I' Q hIQ)
  letI : IsLocalRing (Localization.AtPrime Q ⧸ J') := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J') Ideal.Quotient.mk_surjective
  let a : Fin r → MvPolynomial (Fin r ⊕ Fin c) K :=
    fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.C (y (Sum.inl i))
  have ht := polynomial_firstOrder_tangents_generate_local_quotient
    I' Q hIQ y rfl H hlocal h0H hDH
  have hp := actual_point_parameters_transport_under_coordinates I P Q C hPQ a ht
  have he (i : Fin r) : C.symm (a i) = MvPolynomial.rename e
      (M⁻¹.toMvPolynomial (Sum.inl i) - MvPolynomial.C (y (Sum.inl i))) := by
    change MvPolynomial.rename e (polynomialLinearChange M⁻¹ _) = _
    congr 1
    simp [a, polynomialLinearChange]
  refine ⟨r, fun i => C.symm (a i), hr, ?_, hp⟩
  intro i
  change (C.symm (a i)).totalDegree ≤ 1 ∧ MvPolynomial.eval x (C.symm (a i)) = 0
  rw [he]
  constructor
  · apply (MvPolynomial.totalDegree_rename_le _ _).trans
    rw [sub_eq_add_neg, ← MvPolynomial.C_neg]
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le (Matrix.toMvPolynomial_totalDegree_le _ _) (by simp))
  · simp [MvPolynomial.eval_rename, Matrix.toMvPolynomial_eval_eq_apply, y]

/-- The number of these centered linear parameters equals the actual
differential rank of the original prime quotient, independent of the point. -/
theorem smoothLocus_constructs_original_linear_parameters
    {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (hI : I ≠ ⊥)
    (p : Ideal (MvPolynomial σ K ⧸ I)) [p.IsPrime] [Algebra.IsSmoothAt K p]
    (x : σ → K)
    (hp : p.comap (Ideal.Quotient.mk I) =
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom) :
    let P := p.comap (Ideal.Quotient.mk I)
    let J := I.map (algebraMap _ (Localization.AtPrime P))
    letI : Nontrivial (Localization.AtPrime P ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
      (polynomial_local_ideal_ne_top I P (by
        intro F hF
        change Ideal.Quotient.mk I F ∈ p
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hF]
        exact p.zero_mem))
    letI : IsLocalRing (Localization.AtPrime P ⧸ J) := IsLocalRing.of_surjective'
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    ∃ (r : ℕ) (a : Fin r → MvPolynomial σ K),
      r = Module.finrank (MvPolynomial σ K ⧸ I)
        (KaehlerDifferential K (MvPolynomial σ K ⧸ I)) ∧
      (∀ i, (a i).totalDegree ≤ 1 ∧ MvPolynomial.eval x (a i) = 0) ∧
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk J
        (algebraMap _ (Localization.AtPrime P) (a i)))) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P ⧸ J) := by
  let P := p.comap (Ideal.Quotient.mk I)
  letI : P.IsPrime := inferInstance
  have hIP : I ≤ P := by
    intro F hF
    change Ideal.Quotient.mk I F ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hF]
    exact p.zero_mem
  let J := I.map (algebraMap _ (Localization.AtPrime P))
  letI : Nontrivial (Localization.AtPrime P ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top I P hIP)
  letI : IsLocalRing (Localization.AtPrime P ⧸ J) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  letI : Algebra.FormallySmooth K (Localization.AtPrime P ⧸ J) :=
    quotient_smoothAt_formallySmooth_localized_ideal I p
  have hloc : J ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI
  obtain ⟨r, a, hr, hlinear, ha⟩ := smooth_point_constructs_original_linear_parameters
    I P hIP x hp hloc
  exact ⟨r, a, hr.trans (polynomial_local_differential_finrank I P hIP), hlinear, ha⟩

end LinearStudy
