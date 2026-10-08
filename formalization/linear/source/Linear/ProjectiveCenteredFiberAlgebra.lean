module
public import Linear.PolynomialEquationCoordinateAlgebra
public import Linear.ProjectiveAmbientFiberCompleteIntersection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The exact centered numerators from the ORIGINAL map have a finite
ACTUAL ambient equation quotient after independent source/target coordinates.
No finiteness, reducedness, ideal equality or field-degree formula is input. -/
theorem projective_actual_centered_fiber_algebra_finite
    {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (f : HomogeneousEndomorphism n) (hq : 0 < f.degree) (y : Fin n → ℂ)
    (E : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial τ ℂ) (b : Fin n ≃ τ)
    (M : Matrix τ τ ℂ) (hM : Matrix.det M ≠ 0) :
    let z := M⁻¹ *ᵥ (y ∘ b.symm)
    let p0 := E (affineChartPolynomialMap (f.forms 0))
    let p := fun j => E (affineChartPolynomialMap (f.forms (b.symm j).succ))
    let pC := fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i) - MvPolynomial.C (z i) * p0
    Module.Finite ℂ (MvPolynomial τ ℂ ⧸ Ideal.span (Set.range pC)) := by
  intro z p0 p pC
  let P := projectiveAmbientFiberPolynomials f y
  have hP : P = (fun i : Fin n => affineChartPolynomialMap (f.forms i.succ) -
      MvPolynomial.C (y i) * affineChartPolynomialMap (f.forms 0)) := by
    funext i
    simp only [P,projectiveAmbientFiberPolynomials,projectiveAmbientFiberForms,map_sub,map_mul]
    simp [affineChartPolynomialMap]
  letI : Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range P)) := by
    rw [← projectiveAmbientFiberIdeal_eq_polynomial_span]
    exact projectiveAmbientFiberQuotient_finite f hq y
  have hCentered : pC = fun i => MvPolynomial.aeval
      (fun j => p j - MvPolynomial.C ((y ∘ b.symm) j) * p0) ((M⁻¹).toMvPolynomial i) :=
    matrix_polynomial_centered_numerators M⁻¹ (y ∘ b.symm) p0 p
  have hOriginal : (fun j => p j - MvPolynomial.C ((y ∘ b.symm) j) * p0) =
      (fun j => E (P (b.symm j))) := by
    funext j
    rw [hP]
    simp only [map_sub,map_mul]
    congr 1
    congr 1
    exact (E.commutes (y (b.symm j))).symm
  have hEq : pC = (fun i => MvPolynomial.aeval
      (fun j => E (P (b.symm j))) ((M⁻¹).toMvPolynomial i)) := by
    exact hCentered.trans (congrArg
      (fun a => fun i => MvPolynomial.aeval a ((M⁻¹).toMvPolynomial i)) hOriginal)
  letI := polynomial_equation_coordinate_algebra_finite E b M hM P
  let e := Ideal.quotientEquivAlgOfEq (R₁ := ℂ)
    (congrArg (fun a => Ideal.span (Set.range a)) hEq)
  exact Module.Finite.equiv e.symm.toLinearEquiv

end LinearStudy
