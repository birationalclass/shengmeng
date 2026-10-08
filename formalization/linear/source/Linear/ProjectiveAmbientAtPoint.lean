module
public import Linear.ProjectiveAmbientUnramifiedPoint
public import Linear.ProjectiveGoodAffineCoordinates
public import Linear.RationalLocalEssentialFiniteType
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
variable {n : ℕ}

/-- Transport at a specified rational point, without choosing another witness. -/
theorem projectiveAmbientChart_unramified_at_rational_point
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (ρ : Localization.Away (projectiveChartDenominator f V) →ₐ[ℂ] ℂ)
    (hρ : let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
      letI : Algebra (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (Localization.Away (projectiveChartDenominator f V)) := φ.toRingHom.toAlgebra
      rationalPointPrime ρ ∈ Algebra.unramifiedLocus
        (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (Localization.Away (projectiveChartDenominator f V))) :
    let p0 := affineChartPolynomialMap (f.forms 0)
    let p := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
    let J := V.affineIdeal.map (algebraMap _ (Localization.Away p0))
    let E := awayQuotientEquiv V.affineIdeal p0
    let hI := projectiveRationalPolynomialChartMap_ideal f V hq hf hV x0 hx0
    let ψ := Ideal.quotientMap J (rationalPolynomialChartMap p0 p).toRingHom
      (Ideal.map_le_iff_le_comap.mp hI)
    let P := (rationalPointPrime ρ).asIdeal.comap E.toRingHom
    let Q := P.comap ψ
    (generalPointLocalQuotientPullback V.affineIdeal J
      (P.comap (Ideal.Quotient.mk J)) (Q.comap (Ideal.Quotient.mk V.affineIdeal))
      (rationalPolynomialChartMap p0 p).toRingHom (by ext r; rfl) hI).FormallyUnramified := by
  intro p0 p J E hI ψ P Q
  let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
  let Pρ := (rationalPointPrime ρ).asIdeal
  letI : Pρ.IsPrime := inferInstance
  letI : P.IsPrime := inferInstance
  letI : Q.IsPrime := inferInstance
  have he := projectiveChartOpenMap_ambient_quotient_comp f V hq hf hV x0 hx0
  change E.toRingHom.comp ψ = φ.toRingHom at he
  have ht := rationalPointPrime_comp_formallyUnramified φ ρ hρ
  rw [← he] at ht
  have hl := ringHom_pointwiseUnramified_localRingHom (E.toRingHom.comp ψ) Pρ
    ((Pρ.comap E.toRingHom).comap ψ) (by ext a; rfl) ht
  have hlocal := localRingHom_formallyUnramified_of_equiv_comp ψ E.toRingEquiv Pρ hl
  exact quotientLocalPullback_formallyUnramified V.affineIdeal J
    (rationalPolynomialChartMap p0 p).toRingHom hI P hlocal

/-- The same rational point evaluates the ambient denominator open at its actual coordinates. -/
theorem projectiveChartOpenMap_ambient_rational_evaluation
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (ρ : Localization.Away (projectiveChartDenominator f V) →ₐ[ℂ] ℂ)
    (x : Fin n → ℂ)
    (hx : (ρ.comp (IsScalarTower.toAlgHom ℂ
      (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
      (Localization.Away (projectiveChartDenominator f V)))).comp
        (Ideal.Quotient.mkₐ ℂ V.affineIdeal) = MvPolynomial.aeval x)
    (hp0 : MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)) ≠ 0) :
    let p0 := affineChartPolynomialMap (f.forms 0)
    let J := V.affineIdeal.map (algebraMap _ (Localization.Away p0))
    ρ.comp ((awayQuotientBaseEquiv (K := ℂ) V.affineIdeal p0).toAlgHom.comp
      (Ideal.Quotient.mkₐ ℂ J)) = polynomialAwayPointEvaluation x p0 hp0 := by
  intro p0 J
  apply IsLocalization.algHom_ext (Submonoid.powers p0)
  apply MvPolynomial.algHom_ext
  intro i
  change ρ (awayQuotientEquiv V.affineIdeal p0
    (Ideal.Quotient.mk J (algebraMap _ (Localization.Away p0) (MvPolynomial.X i)))) = _
  rw [awayQuotientEquiv_mk]
  change ρ (algebraMap _ (Localization.Away (projectiveChartDenominator f V))
    (Ideal.Quotient.mk V.affineIdeal (MvPolynomial.X i))) =
    polynomialAwayPointEvaluation x p0 hp0
      (algebraMap _ (Localization.Away p0) (MvPolynomial.X i))
  rw [polynomialAwayPointEvaluation_algebraMap]
  exact AlgHom.congr_fun hx (MvPolynomial.X i)

end LinearStudy
