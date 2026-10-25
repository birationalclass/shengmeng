module
public import Linear.ProjectiveDifferentialDimension
public import Linear.ProjectiveAffineSmoothLocus
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Actual common local generators and original formal normal-ideal data.
This is an explicit output proposition; no conclusions are assumed as inputs. -/
def ProjectiveCommonNormalPresentation {ι : Type*}
    (V : IntegralProjectiveEquations n) (x : ι → Fin n → ℂ)
    (hx : ∀ a, normalizedProjectivePoint (x a) ∈ V.zeroSet) (r c : ℕ) : Prop :=
    ∃ hc : 0 < c,
      letI : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
      ∃ (e : (Fin r ⊕ Fin c) ≃ Fin n)
        (M : Matrix (Fin n) (Fin n) ℂ) (hM : Matrix.det M ≠ 0)
        (G : ι → Fin c → MvPolynomial (Fin n) ℂ),
        let C := polynomialLinearChangeEquiv M hM
        let y : ι → Fin r ⊕ Fin c → ℂ := fun a => (M⁻¹ *ᵥ x a) ∘ e
        let H : ι → Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
          fun a i => MvPolynomial.rename e.symm (C (G a i))
        ∃ (hH : ∀ a i, MvPolynomial.eval (y a) (H a i) = 0)
          (hJ : ∀ a, IsUnit (Matrix.det (fun i j => MvPolynomial.eval (y a)
            (MvPolynomial.pderiv (Sum.inr j) (H a i))))),
          (∀ a, V.affineIdeal.map (algebraMap _ (Localization.AtPrime
              ((V.affinePoint (x a) (hx a)).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)))) =
            Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime
              ((V.affinePoint (x a) (hx a)).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal))) (G a i)))) ∧
          ∀ a, V.affineIdeal.map
            (((polynomialSmoothFormalMap (y a) (H a) (hH a) (hJ a)).comp
              (MvPolynomial.rename e.symm).toRingHom).comp C.toRingHom) =
            Ideal.span (Set.range (MvPowerSeries.X
              (σ := Fin c) (R := MvPowerSeries (Fin r) ℂ)))

/-- Common actual linear coordinates and original formal normal ideals for
ALL members of an original smooth point family, with the tangential dimension
identified with the ACTUAL original chart Krull dimension and differential rank.
Neither the normal equations nor a codimension/dimension formula is input. -/
theorem projective_smooth_points_common_coordinates_actual_dimension
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : IntegralProjectiveEquations n) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x : ι → Fin n → ℂ) (hx : ∀ a, normalizedProjectivePoint (x a) ∈ V.zeroSet)
    [∀ a, Algebra.IsSmoothAt ℂ (V.affinePoint (x a) (hx a)).asIdeal] :
    ∃ (r c : ℕ),
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) = r ∧
      c = n - r ∧ ∃ hc : 0 < c,
      letI : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
      ∃ (e : (Fin r ⊕ Fin c) ≃ Fin n)
        (M : Matrix (Fin n) (Fin n) ℂ) (hM : Matrix.det M ≠ 0)
        (G : ι → Fin c → MvPolynomial (Fin n) ℂ),
        let C := polynomialLinearChangeEquiv M hM
        let y : ι → Fin r ⊕ Fin c → ℂ := fun a => (M⁻¹ *ᵥ x a) ∘ e
        let H : ι → Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
          fun a i => MvPolynomial.rename e.symm (C (G a i))
        ∃ (hH : ∀ a i, MvPolynomial.eval (y a) (H a i) = 0)
          (hJ : ∀ a, IsUnit (Matrix.det (fun i j => MvPolynomial.eval (y a)
            (MvPolynomial.pderiv (Sum.inr j) (H a i))))),
          (∀ a, V.affineIdeal.map (algebraMap _ (Localization.AtPrime
              ((V.affinePoint (x a) (hx a)).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)))) =
            Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime
              ((V.affinePoint (x a) (hx a)).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal))) (G a i)))) ∧
          ∀ a, V.affineIdeal.map
            (((polynomialSmoothFormalMap (y a) (H a) (hH a) (hJ a)).comp
              (MvPolynomial.rename e.symm).toRingHom).comp C.toRingHom) =
            Ideal.span (Set.range (MvPowerSeries.X
              (σ := Fin c) (R := MvPowerSeries (Fin r) ℂ))) := by
  classical
  let a₀ := Classical.arbitrary ι
  letI : V.affineIdeal.IsPrime := V.affineIdeal_isPrime_of_point (x a₀) (hx a₀)
  let p := fun a => (V.affinePoint (x a) (hx a)).asIdeal
  let P := fun a => (p a).comap (Ideal.Quotient.mk V.affineIdeal)
  letI : ∀ a, (P a).IsPrime := fun a => inferInstance
  letI : ∀ a, Algebra.FormallySmooth ℂ
      (Localization.AtPrime (P a) ⧸ V.affineIdeal.map (algebraMap _ (Localization.AtPrime (P a)))) :=
    fun a => quotient_smoothAt_formallySmooth_localized_ideal V.affineIdeal (p a)
  have hIP : ∀ a, V.affineIdeal ≤ P a := by
    intro a z hz
    change Ideal.Quotient.mk V.affineIdeal z ∈ p a
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz]
    exact (p a).zero_mem
  have hP : ∀ a, P a = RingHom.ker (MvPolynomial.aeval (R := ℂ) (x a)).toRingHom :=
    fun a => V.affinePointIdeal_comap (x a) (hx a)
  let r := Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
    (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal))
  let c := n - r
  have hc : 0 < c := by
    have h := smooth_prime_polynomial_conormal_rank_positive V.affineIdeal (P a₀)
      (V.affineIdeal_ne_bot hproper) (hIP a₀)
    simpa only [Nat.card_fin] using h
  letI : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  have hcle : Fintype.card (Fin c) ≤ Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    exact Nat.sub_le n r
  obtain ⟨ν⟩ := Function.Embedding.nonempty_of_card_le hcle
  have hrank : ∀ a, Module.finrank
      (Localization.AtPrime (P a) ⧸ V.affineIdeal.map (algebraMap _ (Localization.AtPrime (P a))))
      (polynomialLocalQuotientExtension V.affineIdeal (P a)).Cotangent = c := by
    intro a
    simpa only [Nat.card_fin] using smooth_polynomial_conormal_finrank V.affineIdeal (P a) (hIP a)
  obtain ⟨G, M, hM, h⟩ := smooth_points_have_common_polynomial_coordinates
    V.affineIdeal P x hIP hP ν ν.injective hrank
  obtain ⟨s, e, he⟩ := exists_coordinate_split ν ν.injective
  have hcard : s + c = n := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e
  have hsr : s = r := by
    dsimp only [c] at hc hcard
    omega
  subst s
  refine ⟨r, c, V.chart_krull_dimension_eq_differential_rank (x a₀) (hx a₀), rfl, rfl,
    hc, e, M, hM, G, ?_⟩
  intro C y H
  have hH : ∀ a i, MvPolynomial.eval (y a) (H a i) = 0 := by
    intro a i
    rw [polynomial_eval_coordinate_equiv]
    exact (h a).2.2.1 i
  have hJ : ∀ a, IsUnit (Matrix.det (fun i j => MvPolynomial.eval (y a)
      (MvPolynomial.pderiv (Sum.inr j) (H a i)))) := by
    intro a
    apply isUnit_iff_ne_zero.mpr
    have hm : (fun (i j : Fin c) => MvPolynomial.eval (y a)
        (MvPolynomial.pderiv (Sum.inr j) (H a i))) =
        (fun (i j : Fin c) => MvPolynomial.eval (M⁻¹ *ᵥ x a)
          (MvPolynomial.pderiv (ν j) (C (G a i)))) := by
      funext i j
      rw [polynomial_derivative_eval_coordinate_equiv, he]
    rw [hm]
    exact (h a).2.2.2
  refine ⟨hH, hJ, (fun a => (h a).1), ?_⟩
  intro a
  let Q := RingHom.ker (MvPolynomial.aeval (R := ℂ) (M⁻¹ *ᵥ x a)).toRingHom
  letI : Q.IsPrime := RingHom.ker_isPrime _
  have hPQ : P a = Q.comap C.toRingHom :=
    (hP a).trans (point_kernel_under_polynomialLinearChange M hM (x a))
  have hs := local_ideal_generators_under_ringEquiv V.affineIdeal (P a) Q
    C.toRingEquiv hPQ (G a) (h a).1
  rw [← Ideal.map_map]
  exact reindexed_smooth_formal_ideal (V.affineIdeal.map C.toRingHom) Q (M⁻¹ *ᵥ x a) rfl
    e (fun i => C (G a i)) (hH a) (hJ a) hs

end LinearStudy
