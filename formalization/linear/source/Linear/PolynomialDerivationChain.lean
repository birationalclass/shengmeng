module
public import Linear.LocalPullbackGenerators
public import Mathlib.Algebra.MvPolynomial.PDeriv
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

theorem polynomial_derivation_chain {K R B σ : Type*}
    [CommRing K] [CommRing R] [CommRing B] [Algebra B R] [Fintype σ]
    (ψ : MvPolynomial σ K →+* R) (D : Derivation B R R)
    (hC : ∀ a : K, D (ψ (MvPolynomial.C a)) = 0)
    (P : MvPolynomial σ K) :
    D (ψ P) = ∑ i, ψ (MvPolynomial.pderiv i P) * D (ψ (MvPolynomial.X i)) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [hC]
  | add p q hp hq =>
      simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
      simp [Derivation.leibniz, smul_eq_mul, hp, Pi.single_apply,
        Finset.mul_sum, mul_comm]
      simp [apply_ite, mul_add, Finset.sum_add_distrib, mul_comm]
      apply Finset.sum_congr rfl
      intro i hi
      ring

variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin c)]

theorem polynomialSmoothFormalMap_C (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (a : K) :
    polynomialSmoothFormalMap x G hG hJ (MvPolynomial.C a) =
      MvPowerSeries.C (MvPowerSeries.C a) := by
  let E := polynomialSmoothCoordinateEquiv x G hG hJ
  change (powerSeriesCoordinateChart K r c).symm (E.symm (formalPolynomialAtPoint x (MvPolynomial.C a))) = _
  rw [formalPolynomialAtPoint_C]
  have hE : E.symm (MvPowerSeries.C a) = MvPowerSeries.C a := E.symm.commutes a
  rw [hE]
  apply (powerSeriesCoordinateChart K r c).injective
  rw [RingEquiv.apply_symm_apply, powerSeriesCoordinateChart_C, MvPowerSeries.rename_C]

theorem polynomialSmoothFormalMap_tangent_derivative (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (i : Fin r) (j : Fin c) :
    MvPowerSeries.pderiv j (polynomialSmoothFormalMap x G hG hJ (MvPolynomial.X (Sum.inl i))) = 0 := by
  have h := polynomialSmoothFormalMap_parameter x G hG hJ i
  rw [map_sub, polynomialSmoothFormalMap_C] at h
  have he := sub_eq_iff_eq_add.mp h
  rw [he]
  simp

theorem polynomialSmoothFormalMap_normal_chain (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (P : MvPolynomial (Fin r ⊕ Fin c) K) (j : Fin c) :
    MvPowerSeries.pderiv j (polynomialSmoothFormalMap x G hG hJ P) =
      ∑ k : Fin c, polynomialSmoothFormalMap x G hG hJ (MvPolynomial.pderiv (Sum.inr k) P) *
        MvPowerSeries.pderiv j (polynomialSmoothFormalMap x G hG hJ (MvPolynomial.X (Sum.inr k))) := by
  rw [polynomial_derivation_chain (polynomialSmoothFormalMap x G hG hJ)
    (MvPowerSeries.pderiv j) (fun a => by rw [polynomialSmoothFormalMap_C]; simp)]
  rw [Fintype.sum_sum_type]
  simp [polynomialSmoothFormalMap_tangent_derivative]

end LinearStudy
