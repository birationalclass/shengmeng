module
public import Linear.OriginalPolynomialNormal
public import Linear.PointLocalCoordinateEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open scoped Matrix
attribute [local instance] polynomialLocalDifferentialModule

/-- Actual point-local smoothness constructs ambient polynomial parameters
of the ORIGINAL local quotient, rather than supplying a parameter span. -/
theorem smooth_point_constructs_original_polynomial_parameters
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
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk J
        (algebraMap _ (Localization.AtPrime P) (a i)))) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P ⧸ J) := by
  classical
  let J := I.map (algebraMap _ (Localization.AtPrime P))
  let : Nontrivial (Localization.AtPrime P ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top I P hIP)
  let : IsLocalRing (Localization.AtPrime P ⧸ J) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  obtain ⟨r, c, hc, e, M, hM, H, hr, h0H, hDH, hlocal⟩ :=
    smooth_point_original_ideal_normal_polynomial_generators I P hIP x hP hI
  let C := (MvPolynomial.renameEquiv K e.symm).toRingEquiv.trans
    (polynomialLinearChangeEquiv M hM).toRingEquiv
  let y := M⁻¹ *ᵥ (x ∘ e)
  let Q := RingHom.ker (MvPolynomial.aeval (R := K) y).toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime _
  have hxy : M *ᵥ y = x ∘ e := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]
  have hPQ : P = Q.comap C.toRingHom := by
    rw [hP]
    ext F
    change MvPolynomial.eval x F = 0 ↔ MvPolynomial.eval y
      (polynomialLinearChange M (MvPolynomial.rename e.symm F)) = 0
    rw [eval_polynomialLinearChange, hxy, polynomial_eval_coordinate_equiv]
  let I' := I.map C.toRingHom
  have hIQ : I' ≤ Q := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [← hPQ]
    exact hIP
  let J' := I'.map (algebraMap _ (Localization.AtPrime Q))
  let : Nontrivial (Localization.AtPrime Q ⧸ J') := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top I' Q hIQ)
  let : IsLocalRing (Localization.AtPrime Q ⧸ J') := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J') Ideal.Quotient.mk_surjective
  let a : Fin r → MvPolynomial (Fin r ⊕ Fin c) K :=
    fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.C (y (Sum.inl i))
  have ht := polynomial_firstOrder_tangents_generate_local_quotient
    I' Q hIQ y rfl H hlocal h0H hDH
  have h := actual_point_parameters_transport_under_coordinates I P Q C hPQ a ht
  exact ⟨r, fun i => C.symm (a i), hr, h⟩
/-- Rational smooth points of the original prime quotient construct polynomial
parameters whose number is the fixed differential rank of that quotient. -/
theorem smoothLocus_constructs_original_polynomial_parameters
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
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk J
        (algebraMap _ (Localization.AtPrime P) (a i)))) =
          IsLocalRing.maximalIdeal (Localization.AtPrime P ⧸ J) := by
  let P := p.comap (Ideal.Quotient.mk I)
  let : P.IsPrime := inferInstance
  have hIP : I ≤ P := by
    intro F hF
    change Ideal.Quotient.mk I F ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hF]
    exact p.zero_mem
  let J := I.map (algebraMap _ (Localization.AtPrime P))
  let : Nontrivial (Localization.AtPrime P ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top I P hIP)
  let : IsLocalRing (Localization.AtPrime P ⧸ J) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : Algebra.FormallySmooth K (Localization.AtPrime P ⧸ J) :=
    quotient_smoothAt_formallySmooth_localized_ideal I p
  have hloc : J ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI
  obtain ⟨r, a, hr, ha⟩ := smooth_point_constructs_original_polynomial_parameters
    I P hIP x hp hloc
  exact ⟨r, a, hr.trans (polynomial_local_differential_finrank I P hIP), ha⟩
end LinearStudy
