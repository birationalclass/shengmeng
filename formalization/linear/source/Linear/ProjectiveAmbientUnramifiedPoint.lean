module
public import Linear.ProjectiveAmbientOpenComparison
public import Linear.QuotientLocalPullbackComparison
public import Linear.LocalMapEquivComparison
public import Linear.ProjectiveChartGoodPoint
public import Linear.UnramifiedLocalRingHom
public import Linear.RationalPointLocalMap
public import Linear.RationalPointUnramifiedComposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
variable {n : ℕ}

/-- The actual ambient rational polynomial local quotient pullback is unramified
at a constructed smooth source point with smooth image. It is not an input. -/
theorem projectiveAmbientChart_exists_unramified_local_quotient
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let A := Localization.Away (projectiveChartDenominator f V)
    let p0 := affineChartPolynomialMap (f.forms 0)
    let p := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
    let J := V.affineIdeal.map (algebraMap _ (Localization.Away p0))
    let E := awayQuotientEquiv V.affineIdeal p0
    let hI := projectiveRationalPolynomialChartMap_ideal f V hq hf hV x hx
    let ψ := Ideal.quotientMap J (rationalPolynomialChartMap p0 p).toRingHom
      (Ideal.map_le_iff_le_comap.mp hI)
    ∃ ρ : A →ₐ[ℂ] ℂ,
      rationalPointPrime ρ ∈ Algebra.smoothLocus ℂ A ∧
      rationalPointPrime (ρ.comp (projectiveChartOpenMap f V hq hf hV x hx)) ∈
        Algebra.smoothLocus ℂ B ∧
      let P := (rationalPointPrime ρ).asIdeal.comap E.toRingHom
      let Q := P.comap ψ
      (generalPointLocalQuotientPullback V.affineIdeal J
        (P.comap (Ideal.Quotient.mk J)) (Q.comap (Ideal.Quotient.mk V.affineIdeal))
        (rationalPolynomialChartMap p0 p).toRingHom (by ext r; rfl) hI).FormallyUnramified := by
  intro B A p0 p J E hI ψ
  let φ := projectiveChartOpenMap f V hq hf hV x hx
  obtain ⟨ρ, hsource, himage, hunram⟩ := projectiveChartOpenMap_exists_good_rational_point f V hq hf hV x hx
  refine ⟨ρ, hsource, himage, ?_⟩
  let P := (rationalPointPrime ρ).asIdeal
  let Pc := P.comap E.toRingHom
  let Qc := Pc.comap ψ
  letI : P.IsPrime := inferInstance
  letI : Pc.IsPrime := inferInstance
  letI : Qc.IsPrime := inferInstance
  have he := projectiveChartOpenMap_ambient_quotient_comp f V hq hf hV x hx
  change E.toRingHom.comp ψ = φ.toRingHom at he
  have ht := rationalPointPrime_comp_formallyUnramified φ ρ hunram
  rw [← he] at ht
  have hl := ringHom_pointwiseUnramified_localRingHom (E.toRingHom.comp ψ) P
    ((P.comap E.toRingHom).comap ψ) (by ext a; rfl) ht
  have hlocal := localRingHom_formallyUnramified_of_equiv_comp ψ E.toRingEquiv P hl
  exact quotientLocalPullback_formallyUnramified V.affineIdeal J
    (rationalPolynomialChartMap p0 p).toRingHom hI Pc hlocal

end LinearStudy
