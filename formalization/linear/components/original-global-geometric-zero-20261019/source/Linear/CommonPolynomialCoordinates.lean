module
public import Linear.CommonNormalCoordinates
public import Linear.PolynomialLinearChange
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open scoped Matrix

/-- A single actual polynomial algebra automorphism has a nonsingular fixed
normal block for all the given polynomial systems at their respective points.
The full-rank hypotheses are on their explicit original derivative matrices. -/
theorem exists_common_polynomial_normal_coordinates {K σ ι : Type*}
    [Field K] [Infinite K] [Fintype σ] [DecidableEq σ] [Fintype ι]
    {c : ℕ} (ν : Fin c → σ) (hν : Function.Injective ν)
    (G : ι → Fin c → MvPolynomial σ K) (x : ι → σ → K)
    (hG : ∀ a, LinearIndependent K
      (fun i j => MvPolynomial.eval (x a) (MvPolynomial.pderiv j (G a i)))) :
    ∃ (P : Matrix σ σ K) (hP : Matrix.det P ≠ 0),
      let e := polynomialLinearChangeEquiv P hP
      ∀ a,
        (∀ i, MvPolynomial.eval (P⁻¹ *ᵥ x a) (e (G a i)) =
          MvPolynomial.eval (x a) (G a i)) ∧
        Matrix.det (fun i k => MvPolynomial.eval (P⁻¹ *ᵥ x a)
          (MvPolynomial.pderiv (ν k) (e (G a i)))) ≠ 0 := by
  let A : ι → Matrix (Fin c) σ K := fun a => Matrix.of
    (fun i j => MvPolynomial.eval (x a) (MvPolynomial.pderiv j (G a i)))
  obtain ⟨P, hP, hN⟩ := exists_common_normal_coordinate_matrix ν hν A hG
  refine ⟨P, hP, ?_⟩
  intro e a
  have hx : P *ᵥ (P⁻¹ *ᵥ x a) = x a := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP),
      Matrix.one_mulVec]
  constructor
  · intro i
    change MvPolynomial.eval (P⁻¹ *ᵥ x a) (polynomialLinearChange P (G a i)) = _
    rw [eval_polynomialLinearChange, hx]
  · have he : (fun (i k : Fin c) => MvPolynomial.eval (P⁻¹ *ᵥ x a)
        (MvPolynomial.pderiv (ν k) (polynomialLinearChange P (G a i)))) =
        ((A a) * P).submatrix id ν := by
      funext i k
      rw [eval_pderiv_polynomialLinearChange, hx]
      rfl
    change Matrix.det (fun (i k : Fin c) => MvPolynomial.eval (P⁻¹ *ᵥ x a)
      (MvPolynomial.pderiv (ν k) (polynomialLinearChange P (G a i)))) ≠ 0
    rw [he]
    exact hN a

end LinearStudy
