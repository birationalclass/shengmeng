module
public import Linear.SmoothCommonCoordinates
public import Linear.LocalGeneratorsEquiv
public import Linear.SmoothReindexedFormalIdeal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open scoped Matrix

/-- The original embedded ideal has formal normal coordinates at ALL chosen
smooth points after the SAME actual ambient polynomial change. The equations,
normal minor, coordinate maps and original-ideal images are constructed.
The common conormal rank and an injective normal-position selection are explicit. -/
theorem smooth_points_have_common_formal_normal_coordinates {K σ ι : Type*}
    [Field K] [Infinite K] [Fintype σ] [DecidableEq σ] [Fintype ι]
    (I : Ideal (MvPolynomial σ K)) (P : ι → Ideal (MvPolynomial σ K))
    [∀ a, (P a).IsPrime] (x : ι → σ → K)
    (hIP : ∀ a, I ≤ P a)
    (hP : ∀ a, P a = RingHom.ker (MvPolynomial.aeval (R := K) (x a)).toRingHom)
    [∀ a, Algebra.FormallySmooth K
      (Localization.AtPrime (P a) ⧸ I.map (algebraMap _ (Localization.AtPrime (P a))))]
    {c : ℕ} [Nonempty (Fin c)] (ν : Fin c → σ) (hν : Function.Injective ν)
    (hc : ∀ a, Module.finrank
      (Localization.AtPrime (P a) ⧸ I.map (algebraMap _ (Localization.AtPrime (P a))))
      (polynomialLocalQuotientExtension I (P a)).Cotangent = c) :
    ∃ (r : ℕ) (e : (Fin r ⊕ Fin c) ≃ σ)
      (M : Matrix σ σ K) (hM : Matrix.det M ≠ 0) (G : ι → Fin c → MvPolynomial σ K),
      let C := polynomialLinearChangeEquiv M hM
      let y : ι → Fin r ⊕ Fin c → K := fun a => (M⁻¹ *ᵥ x a) ∘ e
      let H : ι → Fin c → MvPolynomial (Fin r ⊕ Fin c) K :=
        fun a i => MvPolynomial.rename e.symm (C (G a i))
      ∃ (hH : ∀ a i, MvPolynomial.eval (y a) (H a i) = 0)
        (hJ : ∀ a, IsUnit (Matrix.det (fun i j => MvPolynomial.eval (y a)
          (MvPolynomial.pderiv (Sum.inr j) (H a i))))),
        ∀ a, I.map (((polynomialSmoothFormalMap (y a) (H a) (hH a) (hJ a)).comp
          (MvPolynomial.rename e.symm).toRingHom).comp C.toRingHom) =
          Ideal.span (Set.range (MvPowerSeries.X
            (σ := Fin c) (R := MvPowerSeries (Fin r) K))) := by
  obtain ⟨G, M, hM, h⟩ := smooth_points_have_common_polynomial_coordinates I P x hIP hP ν hν hc
  obtain ⟨r, e, he⟩ := exists_coordinate_split ν hν
  refine ⟨r, e, M, hM, G, ?_⟩
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
  refine ⟨hH, hJ, ?_⟩
  intro a
  let Q := RingHom.ker (MvPolynomial.aeval (R := K) (M⁻¹ *ᵥ x a)).toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime _
  have hPQ : P a = Q.comap C.toRingHom :=
    (hP a).trans (point_kernel_under_polynomialLinearChange M hM (x a))
  have hs := local_ideal_generators_under_ringEquiv I (P a) Q C.toRingEquiv hPQ (G a) (h a).1
  rw [← Ideal.map_map]
  exact reindexed_smooth_formal_ideal (I.map C.toRingHom) Q (M⁻¹ *ᵥ x a) rfl
    e (fun i => C (G a i)) (hH a) (hJ a) hs

end LinearStudy
