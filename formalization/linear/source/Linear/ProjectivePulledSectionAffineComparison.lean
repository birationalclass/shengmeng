module
public import Linear.ProjectivePulledSectionNativeCoverage
public import Linear.QuotientAwayAtUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- The affine image of the ACTUAL pulled homogeneous cut ideal is the
original variety ideal plus the original substituted section equations. -/
theorem projectivePulledLinearSectionIdeal_map_affine
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) :
    (projectivePulledLinearSectionIdeal f V L w).map (affineChartPolynomialMap (K := ℂ)).toRingHom=
      V.affineIdeal ⊔ Ideal.span (Set.range (fun i => affineChartPolynomialMap
        (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))) := by
  rw [projectivePulledLinearSectionIdeal,Ideal.map_sup,Ideal.map_span,← Set.range_comp']
  rfl

/-- Original point avoidance proves that f0 is a UNIT in the whole actual
dehomogenized cut quotient. This does not radicalize the defining ideal. -/
theorem projectivePulledLinearSection_affine_denominator_isUnit
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (havoid : ∀ v : CoordinateVector n,
      v ∈ MvPolynomial.zeroLocus ℂ (projectivePulledLinearSectionIdeal f V L w) →
        v ≠ 0 → MvPolynomial.eval v (f.forms 0) ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      ((projectivePulledLinearSectionIdeal f V L w).map (affineChartPolynomialMap (K := ℂ)).toRingHom)
      (affineChartPolynomialMap (f.forms 0))) := by
  apply polynomialQuotient_isUnit_of_nonvanishing
  intro x hx
  let v : CoordinateVector n := Fin.cases 1 x
  have hvne : v ≠ 0 := by
    intro he
    have hh := congrFun he 0
    simpa [v] using hh
  have hcomp := affineChartPolynomialMap_comp_aeval (K := ℂ) x
  have hv : v ∈ MvPolynomial.zeroLocus ℂ (projectivePulledLinearSectionIdeal f V L w) := by
    intro H hH
    have he := hx (affineChartPolynomialMap H) (Ideal.mem_map_of_mem _ hH)
    have hc := AlgHom.congr_fun hcomp H
    simpa only [AlgHom.comp_apply,MvPolynomial.aeval_eq_eval] using hc.symm.trans he
  have hc := AlgHom.congr_fun hcomp (f.forms 0)
  simpa only [AlgHom.comp_apply,MvPolynomial.aeval_eq_eval] using
    hc.trans_ne (havoid v hv hvne)

/-- The whole actual affine cut quotient is the actual denominator-open
quotient used in the original-f pullback proof. Original ideals and
nilpotents are preserved by this algebra isomorphism. -/
theorem projectivePulledLinearSection_affine_exists_quotient_algEquiv
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (havoid : ∀ v : CoordinateVector n,
      v ∈ MvPolynomial.zeroLocus ℂ (projectivePulledLinearSectionIdeal f V L w) →
        v ≠ 0 → MvPolynomial.eval v (f.forms 0) ≠ 0) :
    Nonempty ((MvPolynomial (Fin n) ℂ ⧸
      (projectivePulledLinearSectionIdeal f V L w).map (affineChartPolynomialMap (K := ℂ)).toRingHom) ≃ₐ[ℂ]
      (Localization.Away (projectiveChartDenominator f V) ⧸
        projectiveNativeChartPullbackEquationIdeal f V (projectiveLinearSectionForms L w))) := by
  let J := Ideal.span (Set.range (fun i => affineChartPolynomialMap
    (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))))
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let p := affineChartPolynomialMap (f.forms 0)
  let A := Localization.Away (projectiveChartDenominator f V)
  have hI := projectivePulledLinearSectionIdeal_map_affine f V L w
  have hp := projectivePulledLinearSection_affine_denominator_isUnit f V L w havoid
  rw [hI] at hp
  obtain ⟨e⟩ := quotientAwayAtUnit_exists_algEquiv (K := ℂ) V.affineIdeal J p hp
  have hJ : (J.map (Ideal.Quotient.mk V.affineIdeal)).map (algebraMap B A)=
      projectiveNativeChartPullbackEquationIdeal f V (projectiveLinearSectionForms L w) := by
    dsimp only [J,projectiveNativeChartPullbackEquationIdeal]
    rw [Ideal.map_span,Ideal.map_span,← Set.range_comp',← Set.range_comp']
  exact ⟨((Ideal.quotientEquivAlgOfEq ℂ hI).trans e).trans
    (Ideal.quotientEquivAlgOfEq ℂ hJ)⟩

/-- On an explicitly constructed nonempty open the WHOLE actual affine
cut quotient is finite and reduced, not only its f0-denominator open. -/
theorem projectivePulledLinearSection_exists_finite_reduced_affine_cuts
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet=V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ, c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
        w 0 ≠ 0 ∧
          _root_.IsReduced (MvPolynomial (Fin n) ℂ ⧸
            (projectivePulledLinearSectionIdeal f V L w).map (affineChartPolynomialMap (K := ℂ)).toRingHom) ∧
          Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸
            (projectivePulledLinearSectionIdeal f V L w).map (affineChartPolynomialMap (K := ℂ)).toRingHom) := by
  obtain ⟨c,hc,hex,hgood⟩ := projectivePulledLinearSection_exists_chart_avoidance_open
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hred,hfin,havoid⟩ := hgood w hw
  let A := Localization.Away (projectiveChartDenominator f V) ⧸
    projectiveNativeChartPullbackEquationIdeal f V (projectiveLinearSectionForms L w)
  letI : _root_.IsReduced A := hred
  letI : Module.Finite ℂ A := hfin
  obtain ⟨e⟩ := projectivePulledLinearSection_affine_exists_quotient_algEquiv f V L w
    (fun v hv hvne => (havoid v hv hvne).2)
  exact ⟨hw0,isReduced_of_injective e.toRingHom e.injective,
    Module.Finite.of_injective e.toLinearMap e.injective⟩

end LinearStudy
