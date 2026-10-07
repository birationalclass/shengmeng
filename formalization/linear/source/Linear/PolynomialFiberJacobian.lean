module
public import Linear.PolynomialDerivationChain
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

theorem polynomial_substitution_quotient_evaluation {K σ : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K)) (F : σ → MvPolynomial σ K) (y : σ → K)
    (hF : ∀ i, F i - MvPolynomial.C (y i) ∈ J) (P : MvPolynomial σ K) :
    Ideal.Quotient.mk J (MvPolynomial.aeval F P) =
      Ideal.Quotient.mk J (MvPolynomial.C (MvPolynomial.eval y P)) := by
  let π := Ideal.Quotient.mk J
  have he : π.comp (MvPolynomial.aeval F).toRingHom =
      π.comp (MvPolynomial.C.comp (MvPolynomial.eval y)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [π]
    · intro i
      have h : π (F i - MvPolynomial.C (y i)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (hF i)
      rw [map_sub, sub_eq_zero] at h
      simpa [π] using h
  exact RingHom.congr_fun he P

theorem polynomial_pullback_normal_derivative_quotient {K : Type*} [CommRing K]
    {r c : ℕ}
    (J : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (y : Fin r ⊕ Fin c → K) (hF : ∀ i, F i - MvPolynomial.C (y i) ∈ J)
    (H : MvPolynomial (Fin r ⊕ Fin c) K)
    (htan : ∀ i, MvPolynomial.eval y (MvPolynomial.pderiv (Sum.inl i) H) = 0)
    (j : Fin c) :
    Ideal.Quotient.mk J (MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.aeval F H)) =
      ∑ i : Fin c, Ideal.Quotient.mk J
        (MvPolynomial.C (MvPolynomial.eval y (MvPolynomial.pderiv (Sum.inr i) H))) *
          Ideal.Quotient.mk J (MvPolynomial.pderiv (Sum.inr j) (F (Sum.inr i))) := by
  have h := polynomial_derivation_chain (B := K) (MvPolynomial.aeval F).toRingHom
    (MvPolynomial.pderiv (Sum.inr j))
    (fun a => by simp) H
  have hh := congrArg (Ideal.Quotient.mk J) h
  rw [map_sum, Fintype.sum_sum_type] at hh
  change Ideal.Quotient.mk J (MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.aeval F H)) =
    (∑ i : Fin r, Ideal.Quotient.mk J
      (MvPolynomial.aeval F (MvPolynomial.pderiv (Sum.inl i) H) *
        MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.aeval F (MvPolynomial.X (Sum.inl i))))) +
    (∑ i : Fin c, Ideal.Quotient.mk J
      (MvPolynomial.aeval F (MvPolynomial.pderiv (Sum.inr i) H) *
        MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.aeval F (MvPolynomial.X (Sum.inr i))))) at hh
  simp only [map_mul, MvPolynomial.aeval_X] at hh
  have hz : (∑ i : Fin r, Ideal.Quotient.mk J
      (MvPolynomial.aeval F (MvPolynomial.pderiv (Sum.inl i) H)) *
        Ideal.Quotient.mk J (MvPolynomial.pderiv (Sum.inr j) (F (Sum.inl i)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [polynomial_substitution_quotient_evaluation J F y hF, htan i]
    simp
  rw [hz, zero_add] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro i hi
  rw [polynomial_substitution_quotient_evaluation J F y hF]

theorem polynomial_pullback_normal_jacobian_quotient {K : Type*} [CommRing K]
    {r c : ℕ}
    (J : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (y : Fin r ⊕ Fin c → K) (hF : ∀ i, F i - MvPolynomial.C (y i) ∈ J)
    (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (htan : ∀ i j, MvPolynomial.eval y (MvPolynomial.pderiv (Sum.inl j) (H i)) = 0) :
    Ideal.Quotient.mk J (Matrix.det (fun i j =>
      MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.aeval F (H i)))) =
      Ideal.Quotient.mk J (MvPolynomial.C (Matrix.det (fun i j =>
        MvPolynomial.eval y (MvPolynomial.pderiv (Sum.inr j) (H i))))) *
      Ideal.Quotient.mk J (Matrix.det (fun i j =>
        MvPolynomial.pderiv (Sum.inr j) (F (Sum.inr i)))) := by
  let π := Ideal.Quotient.mk J
  let M : Matrix (Fin c) (Fin c) K := fun i j =>
    MvPolynomial.eval y (MvPolynomial.pderiv (Sum.inr j) (H i))
  let N : Matrix (Fin c) (Fin c) (MvPolynomial (Fin r ⊕ Fin c) K) := fun i j =>
    MvPolynomial.pderiv (Sum.inr j) (F (Sum.inr i))
  have he : (Matrix.of fun i j => π (MvPolynomial.pderiv (Sum.inr j)
      (MvPolynomial.aeval F (H i)))) =
      (π.comp MvPolynomial.C).mapMatrix M * π.mapMatrix N := by
    funext i j
    exact polynomial_pullback_normal_derivative_quotient J F y hF (H i) (htan i) j
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det] at hd
  rw [RingHom.map_det π]
  exact hd

theorem polynomial_pullback_normal_jacobian_quotient_span {K : Type*} [CommRing K]
    {r c : ℕ} (J : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (y : Fin r ⊕ Fin c → K) (hF : ∀ i, F i - MvPolynomial.C (y i) ∈ J)
    (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (htan : ∀ i j, MvPolynomial.eval y (MvPolynomial.pderiv (Sum.inl j) (H i)) = 0)
    (hJac : IsUnit (Matrix.det (fun i j =>
      MvPolynomial.eval y (MvPolynomial.pderiv (Sum.inr j) (H i))))) :
    Ideal.span {Ideal.Quotient.mk J (Matrix.det (fun i j =>
      MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.aeval F (H i))))} =
    Ideal.span {Ideal.Quotient.mk J (Matrix.det (fun i j =>
      MvPolynomial.pderiv (Sum.inr j) (F (Sum.inr i))))} := by
  rw [polynomial_pullback_normal_jacobian_quotient J F y hF H htan]
  exact Ideal.span_singleton_mul_left_unit
    ((Ideal.Quotient.mk J).isUnit_map (MvPolynomial.C.isUnit_map hJac)) _

theorem polynomial_pullback_normal_jacobian_image_factor {K R : Type*}
    [CommRing K] [CommRing R] {r c : ℕ}
    (J : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (y : Fin r ⊕ Fin c → K) (hF : ∀ i, F i - MvPolynomial.C (y i) ∈ J)
    (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (htan : ∀ i j, MvPolynomial.eval y (MvPolynomial.pderiv (Sum.inl j) (H i)) = 0)
    (hJac : IsUnit (Matrix.det (fun i j =>
      MvPolynomial.eval y (MvPolynomial.pderiv (Sum.inr j) (H i)))))
    (φ : (MvPolynomial (Fin r ⊕ Fin c) K ⧸ J) →+* R) :
    ∃ u : Rˣ, φ (Ideal.Quotient.mk J (Matrix.det (fun i j =>
      MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.aeval F (H i))))) =
      (u : R) * φ (Ideal.Quotient.mk J (Matrix.det (fun i j =>
        MvPolynomial.pderiv (Sum.inr j) (F (Sum.inr i))))) := by
  let a := Matrix.det (fun i j =>
    MvPolynomial.eval y (MvPolynomial.pderiv (Sum.inr j) (H i)))
  obtain ⟨u, hu⟩ := φ.isUnit_map
    ((Ideal.Quotient.mk J).isUnit_map (MvPolynomial.C.isUnit_map hJac))
  refine ⟨u, ?_⟩
  rw [polynomial_pullback_normal_jacobian_quotient J F y hF H htan, map_mul, hu]

end LinearStudy
