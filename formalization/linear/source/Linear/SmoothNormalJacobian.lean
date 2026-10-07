module
public import Linear.PolynomialDerivationChain
public import Mathlib.RingTheory.Ideal.Span
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin c)]

def smoothNormalCoordinateJacobian (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    Matrix (Fin c) (Fin c) (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) :=
  fun i j => MvPowerSeries.pderiv j
    (polynomialSmoothFormalMap x G hG hJ (MvPolynomial.X (Sum.inr i)))

theorem smooth_normal_jacobian_matrix (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (P : Fin c → MvPolynomial (Fin r ⊕ Fin c) K) :
    (fun i j => MvPowerSeries.pderiv j (polynomialSmoothFormalMap x G hG hJ (P i))) =
      (Matrix.of fun i j => polynomialSmoothFormalMap x G hG hJ (MvPolynomial.pderiv (Sum.inr j) (P i))) *
        smoothNormalCoordinateJacobian x G hG hJ := by
  funext i j
  exact polynomialSmoothFormalMap_normal_chain x G hG hJ (P i) j

theorem smooth_normal_coordinate_jacobian_inverse (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    (Matrix.of fun i j => polynomialSmoothFormalMap x G hG hJ (MvPolynomial.pderiv (Sum.inr j) (G i))) *
      smoothNormalCoordinateJacobian x G hG hJ = 1 := by
  rw [← smooth_normal_jacobian_matrix x G hG hJ G]
  ext i j
  rw [polynomialSmoothFormalMap_equation]
  simp [MvPowerSeries.pderiv_X, Pi.single_apply, Matrix.one_apply]

theorem smooth_normal_coordinate_jacobian_det_unit (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    IsUnit (Matrix.det (smoothNormalCoordinateJacobian x G hG hJ)) := by
  have h := congrArg Matrix.det (smooth_normal_coordinate_jacobian_inverse x G hG hJ)
  rw [Matrix.det_mul, Matrix.det_one] at h
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Matrix.det (fun i j => polynomialSmoothFormalMap x G hG hJ
    (MvPolynomial.pderiv (Sum.inr j) (G i))), ?_⟩
  exact (mul_comm _ _).trans h

theorem smooth_normal_jacobian_det_factor (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (P : Fin c → MvPolynomial (Fin r ⊕ Fin c) K) :
    Matrix.det (fun i j => MvPowerSeries.pderiv j (polynomialSmoothFormalMap x G hG hJ (P i))) =
      polynomialSmoothFormalMap x G hG hJ (Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (P i))) *
        Matrix.det (smoothNormalCoordinateJacobian x G hG hJ) := by
  rw [smooth_normal_jacobian_matrix, Matrix.det_mul]
  congr 1
  exact (RingHom.map_det (polynomialSmoothFormalMap x G hG hJ)
    (Matrix.of fun i j => MvPolynomial.pderiv (Sum.inr j) (P i))).symm

theorem smooth_normal_jacobian_quotient_span (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (P : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (J : Ideal (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K))) :
    Ideal.span {Ideal.Quotient.mk J (Matrix.det (fun i j =>
      MvPowerSeries.pderiv j (polynomialSmoothFormalMap x G hG hJ (P i))))} =
      Ideal.span {Ideal.Quotient.mk J (polynomialSmoothFormalMap x G hG hJ
        (Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (P i))))} := by
  rw [smooth_normal_jacobian_det_factor, map_mul]
  exact Ideal.span_singleton_mul_right_unit
    ((Ideal.Quotient.mk J).isUnit_map (smooth_normal_coordinate_jacobian_det_unit x G hG hJ)) _

theorem smooth_normal_polynomial_jacobian_nonzero (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (P : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (J : Ideal (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)))
    (hne : Ideal.Quotient.mk J (Matrix.det (fun i j =>
      MvPowerSeries.pderiv j (polynomialSmoothFormalMap x G hG hJ (P i)))) ≠ 0) :
    Ideal.Quotient.mk J (polynomialSmoothFormalMap x G hG hJ
      (Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (P i)))) ≠ 0 := by
  rw [smooth_normal_jacobian_det_factor, map_mul] at hne
  intro hz
  exact hne (by rw [hz, zero_mul])

end LinearStudy
