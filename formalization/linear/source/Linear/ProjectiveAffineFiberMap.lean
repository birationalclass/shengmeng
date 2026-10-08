module
public import Linear.ProjectiveAffineFiberUnit
public import Linear.ProjectiveChartPointEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {n : ℕ}

/-- The actual quotient map from V's source chart to its affine fiber. -/
def projectiveAffineFiberCoordinateMap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (y : Fin n → ℂ) :
    (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) →ₐ[ℂ]
      (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) :=
  Ideal.Quotient.factorₐ ℂ (show V.affineIdeal ≤ projectiveAffineFiberIdeal f V y from le_sup_left)

/-- The fiber map from the original denominator chart, using the proved unit. -/
def projectiveAffineFiberChartMap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (y : Fin n → ℂ) :
    Localization.Away (projectiveChartDenominator f V) →ₐ[ℂ]
      (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) :=
  IsLocalization.Away.liftAlgHom (projectiveChartDenominator f V)
    (f := projectiveAffineFiberCoordinateMap f V y)
    (projectiveAffineFiberQuotient_denominator_isUnit f V y)

theorem projectiveAffineFiberChartMap_algebraMap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (y : Fin n → ℂ)
    (b : MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) :
    projectiveAffineFiberChartMap f V y
      (algebraMap _ (Localization.Away (projectiveChartDenominator f V)) b) =
      projectiveAffineFiberCoordinateMap f V y b := by
  simp [projectiveAffineFiberChartMap]

theorem projectiveAffineFiberChartMap_surjective
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (y : Fin n → ℂ) :
    Function.Surjective (projectiveAffineFiberChartMap f V y) := by
  intro b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨algebraMap _ (Localization.Away (projectiveChartDenominator f V))
    (Ideal.Quotient.mk V.affineIdeal p), ?_⟩
  exact projectiveAffineFiberChartMap_algebraMap f V y _

/-- Actual pullback followed by the actual fiber quotient is evaluation at
the target, followed by scalar inclusion. No replacement map is assumed. -/
theorem projectiveAffineFiberChartMap_pullback
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (y : Fin n → ℂ)
    (hy : normalizedProjectivePoint y ∈ V.zeroSet) :
    (projectiveAffineFiberChartMap f V y).comp
      (projectiveChartOpenMap f V hq hf hV y hy) =
      (Algebra.ofId ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y)).comp
        (V.affinePointEvaluation y hy) := by
  let I := projectiveAffineFiberIdeal f V y
  let Q := MvPolynomial (Fin n) ℂ ⧸ I
  let ψ := projectiveAffineFiberChartMap f V y
  have he (i : Fin n) :
      Ideal.Quotient.mk I (affineChartPolynomialMap (f.forms i.succ)) =
        algebraMap ℂ Q (y i) * Ideal.Quotient.mk I (affineChartPolynomialMap (f.forms 0)) := by
    have hmem : affineChartPolynomialMap (f.forms i.succ) -
        MvPolynomial.C (y i) * affineChartPolynomialMap (f.forms 0) ∈ I :=
      Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_sub, map_mul, sub_eq_zero] at hz
    exact hz
  have hinv : Ideal.Quotient.mk I (affineChartPolynomialMap (f.forms 0)) *
      ψ (IsLocalization.Away.invSelf (projectiveChartDenominator f V)) = 1 := by
    have h := congrArg ψ (IsLocalization.Away.mul_invSelf (projectiveChartDenominator f V)
      (S := Localization.Away (projectiveChartDenominator f V)))
    rw [map_mul, map_one, projectiveAffineFiberChartMap_algebraMap] at h
    exact h
  have hcomp : ((projectiveAffineFiberChartMap f V y).comp
      (projectiveChartOpenMap f V hq hf hV y hy)).comp (Ideal.Quotient.mkₐ ℂ V.affineIdeal) =
      ((Algebra.ofId ℂ Q).comp (V.affinePointEvaluation y hy)).comp
        (Ideal.Quotient.mkₐ ℂ V.affineIdeal) := by
    apply MvPolynomial.algHom_ext
    intro i
    change ψ (projectiveChartOpenMap f V hq hf hV y hy
      (Ideal.Quotient.mk V.affineIdeal (MvPolynomial.X i))) =
        algebraMap ℂ Q (V.affinePointEvaluation y hy
          (Ideal.Quotient.mk V.affineIdeal (MvPolynomial.X i)))
    rw [projectiveChartOpenMap_mk, V.affinePointEvaluation_mk]
    simp only [projectiveChartOpenPolynomialMap, MvPolynomial.aeval_X, MvPolynomial.eval_X]
    rw [map_mul, projectiveAffineFiberChartMap_algebraMap]
    change Ideal.Quotient.mk I (affineChartPolynomialMap (f.forms i.succ)) *
      ψ (IsLocalization.Away.invSelf (projectiveChartDenominator f V)) = algebraMap ℂ Q (y i)
    rw [he, mul_assoc, hinv, mul_one]
  apply AlgHom.ext
  intro b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact AlgHom.congr_fun hcomp p

end LinearStudy
