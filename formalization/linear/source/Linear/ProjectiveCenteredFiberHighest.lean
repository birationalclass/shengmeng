module
public import Linear.MatrixPolynomialHighest
public import Linear.ActualCoordinateFiberPoints
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open scoped Matrix

theorem projective_actual_centered_fiber_polynomials
    {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (f : HomogeneousEndomorphism n) (y : Fin n → ℂ)
    (E : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial τ ℂ)
    (eT : τ ≃ Fin n) (M : Matrix τ τ ℂ) :
    let z := M⁻¹ *ᵥ (y ∘ eT)
    let p0 := E (affineChartPolynomialMap (f.forms 0))
    let p := fun j => E (affineChartPolynomialMap (f.forms (eT j).succ))
    (fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i) - MvPolynomial.C (z i) * p0) =
      (fun i => MvPolynomial.aeval (fun j => E (projectiveAmbientFiberPolynomials f y (eT j)))
        ((M⁻¹).toMvPolynomial i)) := by
  intro z p0 p
  have hP : projectiveAmbientFiberPolynomials f y = (fun i : Fin n =>
      affineChartPolynomialMap (f.forms i.succ) -
        MvPolynomial.C (y i) * affineChartPolynomialMap (f.forms 0)) := by
    funext i
    simp only [projectiveAmbientFiberPolynomials,projectiveAmbientFiberForms,map_sub,map_mul]
    simp [affineChartPolynomialMap]
  have hc := matrix_polynomial_centered_numerators M⁻¹ (y ∘ eT) p0 p
  simp only [MvPolynomial.algebraMap_eq] at hc
  have ho : (fun j => p j - MvPolynomial.C ((y ∘ eT) j) * p0) =
      (fun j => E (projectiveAmbientFiberPolynomials f y (eT j))) := by
    funext j
    rw [hP]
    simp only [map_sub,map_mul]
    congr 1
    congr 1
    exact (E.commutes (y (eT j))).symm
  rw [ho] at hc
  exact hc

/-- Insert the actual ORIGINAL highest system into the SAME centered
numerators used by the common Jacobian. Source and target coordinates are
independent actual linear systems; no transformed degree/origin assumption. -/
theorem projective_linear_centered_fiber_highest
    {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (f : HomogeneousEndomorphism n) (y : Fin n → ℂ)
    (MS : Matrix (Fin n) (Fin n) ℂ) (hMS : Matrix.det MS ≠ 0)
    (eS eT : τ ≃ Fin n) (M : Matrix τ τ ℂ) (hM : Matrix.det M ≠ 0)
    (hdegree : ∀ i, (projectiveAmbientFiberPolynomials f y i).totalDegree = f.degree)
    (hz : MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range (fun i =>
      MvPolynomial.homogeneousComponent f.degree (projectiveAmbientFiberPolynomials f y i)))) = {0}) :
    let E := (polynomialLinearChangeEquiv MS hMS).trans (MvPolynomial.renameEquiv ℂ eS.symm)
    let z := M⁻¹ *ᵥ (y ∘ eT)
    let p0 := E (affineChartPolynomialMap (f.forms 0))
    let p := fun j => E (affineChartPolynomialMap (f.forms (eT j).succ))
    let Pc := fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i) - MvPolynomial.C (z i) * p0
    (∀ i, (Pc i).totalDegree ≤ f.degree) ∧
      MvPolynomial.zeroLocus ℂ (Ideal.span (Set.range
        (fun i => MvPolynomial.homogeneousComponent f.degree (Pc i)))) = {0} := by
  intro E z p0 p Pc
  have hPc : Pc = (fun i => MvPolynomial.aeval
      (fun j => E (projectiveAmbientFiberPolynomials f y (eT j))) ((M⁻¹).toMvPolynomial i)) :=
    projective_actual_centered_fiber_polynomials f y E eT M
  have hEd (G : MvPolynomial (Fin n) ℂ) : (E G).totalDegree = G.totalDegree := by
    change (MvPolynomial.renameEquiv ℂ eS.symm (polynomialLinearChangeEquiv MS hMS G)).totalDegree =
      G.totalDegree
    rw [MvPolynomial.totalDegree_renameEquiv,polynomialLinearChangeEquiv_totalDegree]
  have hE (G : MvPolynomial (Fin n) ℂ) :
      MvPolynomial.homogeneousComponent f.degree (E G) = E (MvPolynomial.homogeneousComponent f.degree G) :=
    polynomial_linear_reindex_homogeneousComponent MS hMS eS.symm f.degree G
  have h0 (j : τ) : MvPolynomial.eval (0 : Fin n → ℂ) (E.symm (MvPolynomial.X j)) = 0 := by
    have h := linear_reindexed_actual_source_point MS hMS eS (0 : Fin n → ℂ)
    have hj := congrFun h j
    simpa only [E, Matrix.mulVec_zero, Function.comp_def, Pi.zero_apply] using hj
  rw [hPc]
  refine ⟨?_,?_⟩
  · intro i
    exact matrix_polynomial_combination_totalDegree_le M⁻¹
      (fun j => E (projectiveAmbientFiberPolynomials f y (eT j))) f.degree
      (fun j => by rw [hEd,hdegree]) i
  · exact polynomial_equation_coordinates_highest_zeroLocus E eT.symm M hM
      (projectiveAmbientFiberPolynomials f y) f.degree hE h0 hz

end LinearStudy
