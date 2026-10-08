module
public import Linear.ProjectiveCenteredFiberAlgebra
public import Linear.PolynomialReducedPointCount
public import Linear.PolynomialCoordinatePoints
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

theorem polynomial_equation_coordinate_ideal
    {K σ τ : Type*} [Field K] [Fintype τ] [DecidableEq τ]
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (b : σ ≃ τ)
    (M : Matrix τ τ K) (hM : Matrix.det M ≠ 0) (P : σ → MvPolynomial σ K) :
    Ideal.span (Set.range (fun i => MvPolynomial.aeval
      (fun j => E (P (b.symm j))) ((M⁻¹).toMvPolynomial i))) =
      (Ideal.span (Set.range P)).map E.toRingHom := by
  rw [ideal_span_invertible_matrix_polynomial_combination M hM]
  rw [Ideal.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨P (b.symm j),Set.mem_range_self _,rfl⟩
  · rintro ⟨F,⟨i,rfl⟩,rfl⟩
    exact ⟨b i,by simp⟩

/-- Exact ideal equality for the ORIGINAL centered numerators, preserving
the full ambient normal nilpotents. This is stronger than zero-set equality. -/
theorem projective_actual_centered_fiber_ideal
    {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (f : HomogeneousEndomorphism n) (y : Fin n → ℂ)
    (E : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial τ ℂ) (b : Fin n ≃ τ)
    (M : Matrix τ τ ℂ) (hM : Matrix.det M ≠ 0) :
    let z := M⁻¹ *ᵥ (y ∘ b.symm)
    let p0 := E (affineChartPolynomialMap (f.forms 0))
    let p := fun j => E (affineChartPolynomialMap (f.forms (b.symm j).succ))
    let pC := fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i) - MvPolynomial.C (z i) * p0
    Ideal.span (Set.range pC) = (projectiveAmbientFiberIdeal f y).map E.toRingHom := by
  intro z p0 p pC
  let P := projectiveAmbientFiberPolynomials f y
  have hP : P = (fun i : Fin n => affineChartPolynomialMap (f.forms i.succ) -
      MvPolynomial.C (y i) * affineChartPolynomialMap (f.forms 0)) := by
    funext i
    simp only [P,projectiveAmbientFiberPolynomials,projectiveAmbientFiberForms,map_sub,map_mul]
    simp [affineChartPolynomialMap]
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
  rw [hCentered,hOriginal,projectiveAmbientFiberIdeal_eq_polynomial_span]
  exact polynomial_equation_coordinate_ideal E b M hM P

/-- Every actual scalar point of the changed equation quotient recovers an
actual point of the ORIGINAL equation zero locus, with inverse coordinates. -/
theorem polynomial_quotient_coordinate_actual_zero
    {K σ τ : Type*} [Field K]
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K)
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ K))
    (hJ : J = I.map E.toRingHom) (q : (MvPolynomial τ K ⧸ J) →ₐ[K] K) :
    let u := fun j => q (Ideal.Quotient.mk J (MvPolynomial.X j))
    let x := fun i => MvPolynomial.eval u (E (MvPolynomial.X i))
    x ∈ MvPolynomial.zeroLocus K I ∧
      (fun j => MvPolynomial.eval x (E.symm (MvPolynomial.X j))) = u := by
  intro u x
  have he : MvPolynomial.aeval (R := K) u = q.comp (Ideal.Quotient.mkₐ K J) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [u]
  have hcomp : (MvPolynomial.aeval (R := K) x).comp E.symm.toAlgHom =
      MvPolynomial.aeval u := by
    simpa only [AlgEquiv.symm_symm] using polynomial_coordinate_point_evaluation E.symm u
  have hv (F : MvPolynomial σ K) : MvPolynomial.eval x F = MvPolynomial.eval u (E F) := by
    have h := AlgHom.congr_fun hcomp (E F)
    change MvPolynomial.eval x (E.symm (E F)) = MvPolynomial.eval u (E F) at h
    rw [E.symm_apply_apply] at h
    exact h
  refine ⟨?_, ?_⟩
  · intro F hF
    change MvPolynomial.eval x F = 0
    rw [hv]
    change MvPolynomial.aeval (R := K) u (E F) = 0
    rw [he]
    have hEF : E F ∈ J := by rw [hJ]; exact Ideal.mem_map_of_mem E.toRingHom hF
    change q (Ideal.Quotient.mk J (E F)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hEF,map_zero]
  · funext j
    have h := AlgHom.congr_fun hcomp (MvPolynomial.X j)
    change MvPolynomial.eval x (E.symm (MvPolynomial.X j)) = MvPolynomial.eval u (MvPolynomial.X j) at h
    simpa using h

theorem polynomial_quotient_hom_eq_of_coordinates
    {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (q₁ q₂ : (MvPolynomial σ K ⧸ I) →ₐ[K] K)
    (h : ∀ j, q₁ (Ideal.Quotient.mk I (MvPolynomial.X j)) =
      q₂ (Ideal.Quotient.mk I (MvPolynomial.X j))) : q₁ = q₂ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

end LinearStudy
