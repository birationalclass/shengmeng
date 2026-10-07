module
public import Linear.OriginalIdealFirstOrder
public import Linear.SmoothLocusCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open scoped Matrix

/-- Smoothness of an actual point constructs first-order normal generators
of the ORIGINAL ideal. No local equations or tangent-derivative conditions
are supplied as assumptions. -/
theorem smooth_point_original_ideal_firstOrder_normal_form
    {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P) (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (hI : I.map (algebraMap _ (Localization.AtPrime P)) ≠ ⊥)
    [Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))] :
    ∃ (r c : ℕ) (hc : 0 < c),
      letI : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
      ∃ (e : (Fin r ⊕ Fin c) ≃ σ)
        (M : Matrix (Fin r ⊕ Fin c) (Fin r ⊕ Fin c) K) (hM : Matrix.det M ≠ 0)
        (H : Fin c → MvPowerSeries (Fin r ⊕ Fin c) K),
        (∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) K)) ^ 2) ∧
        I.map (((formalPolynomialAtPoint (M⁻¹ *ᵥ (x ∘ e))).comp
          (polynomialLinearChangeEquiv M hM).toRingHom).comp
            (MvPolynomial.rename e.symm).toRingHom) = Ideal.span (Set.range H) := by
  classical
  obtain ⟨r, c, e, G, hs, h0, hJ⟩ :=
    smooth_generators_exist_with_normal_coordinate_minor I P hIP x hP
  have hc : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro hc
    subst c
    apply hI
    simpa using hs
  let : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
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
  obtain ⟨M, hM, H, hfirst, hideal⟩ := original_local_ideal_firstOrder_normal_form
    (I.map E.toRingHom) y (fun i => E (G i)) hsE h0 hJ
  refine ⟨r, c, hc, e, M, hM, H, hfirst, ?_⟩
  rw [Ideal.map_map] at hideal
  exact hideal

/-- Use the library's actual smooth-point predicate on the original prime
quotient to construct first-order normal equations in ambient coordinates. -/
theorem smoothLocus_point_original_ideal_firstOrder_normal_form
    {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (hI : I ≠ ⊥)
    (p : Ideal (MvPolynomial σ K ⧸ I)) [p.IsPrime] [Algebra.IsSmoothAt K p]
    (x : σ → K)
    (hp : p.comap (Ideal.Quotient.mk I) =
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom) :
    ∃ (r c : ℕ) (hc : 0 < c),
      letI : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
      ∃ (e : (Fin r ⊕ Fin c) ≃ σ)
        (M : Matrix (Fin r ⊕ Fin c) (Fin r ⊕ Fin c) K) (hM : Matrix.det M ≠ 0)
        (H : Fin c → MvPowerSeries (Fin r ⊕ Fin c) K),
        (∀ i, H i - MvPowerSeries.X (Sum.inr i) ∈
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) K)) ^ 2) ∧
        I.map (((formalPolynomialAtPoint (M⁻¹ *ᵥ (x ∘ e))).comp
          (polynomialLinearChangeEquiv M hM).toRingHom).comp
            (MvPolynomial.rename e.symm).toRingHom) = Ideal.span (Set.range H) := by
  let P := p.comap (Ideal.Quotient.mk I)
  let : P.IsPrime := inferInstance
  have hIP : I ≤ P := by
    intro F hF
    change Ideal.Quotient.mk I F ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hF]
    exact p.zero_mem
  let : Algebra.FormallySmooth K
      (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))) :=
    quotient_smoothAt_formallySmooth_localized_ideal I p
  have hloc : I.map (algebraMap _ (Localization.AtPrime P)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hI
  exact smooth_point_original_ideal_firstOrder_normal_form I P hIP x hp hloc
end LinearStudy
