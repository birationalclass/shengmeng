module
public import Linear.ProjectiveCoordinateUnramified
public import Linear.ProjectiveSmoothPointParameters
public import Linear.GeneralUnramifiedPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option Elab.async false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Polynomial target parameters and their actual source pullbacks at a fixed
coordinate witness. The point-dependent localization instances are scoped here. -/
def ProjectiveChartPolynomialParameterConclusion
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (hp0 : MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)) ≠ 0)
    (hy : normalizedProjectivePoint (fun i : Fin n =>
      MvPolynomial.eval x (affineChartPolynomialMap (f.forms i.succ)) /
        MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0))) ∈ V.zeroSet) : Prop :=
    let p0 := affineChartPolynomialMap (f.forms 0)
    let p := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
    let J := V.affineIdeal.map (algebraMap _ (Localization.Away p0))
    let y := fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0
    let P := (rationalPointPrime (polynomialAwayPointEvaluation x p0 hp0)).asIdeal
    let Q := (V.affinePoint y hy).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)
    let L := V.affineIdeal.map (algebraMap _ (Localization.AtPrime Q))
    let M := J.map (algebraMap _ (Localization.AtPrime P))
    ∃ (r : ℕ) (a : Fin r → MvPolynomial (Fin n) ℂ),
      r = Module.finrank (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (KaehlerDifferential ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)) ∧
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk L
        (algebraMap _ (Localization.AtPrime Q) (a i)))) =
          (Q.map (algebraMap _ (Localization.AtPrime Q))).map (Ideal.Quotient.mk L) ∧
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk M
        (algebraMap _ (Localization.AtPrime P) (rationalPolynomialChartMap p0 p (a i))))) =
          (P.map (algebraMap _ (Localization.AtPrime P))).map (Ideal.Quotient.mk M)

/-- Original projective hypotheses construct target polynomial parameters whose
actual rational pullbacks generate the SAME source local maximal ideal. -/
theorem projectiveChart_exists_actual_polynomial_local_parameters
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (hproper : V.ideal.toIdeal ≠ ⊥)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    let p0 := affineChartPolynomialMap (f.forms 0)
    let p := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
    let J := V.affineIdeal.map (algebraMap _ (Localization.Away p0))
    ∃ (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet)
      (hp0 : MvPolynomial.eval x p0 ≠ 0),
      let y := fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0
      ∃ hy : normalizedProjectivePoint y ∈ V.zeroSet,
        Algebra.IsSmoothAt ℂ (V.affinePoint x hx).asIdeal ∧
        Algebra.IsSmoothAt ℂ (V.affinePoint y hy).asIdeal ∧
        ProjectiveChartPolynomialParameterConclusion f V x hx hp0 hy := by
  intro p0 p J
  have hpoint := projectiveChart_exists_smooth_unramified_coordinate_point f V hq hf hV x0 hx0
  dsimp only at hpoint
  obtain ⟨x, hx, hp0, hy, hs, ht, hu⟩ := hpoint
  let y := fun i : Fin n => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0
  let P := (rationalPointPrime (polynomialAwayPointEvaluation x p0 hp0)).asIdeal
  let Q := (V.affinePoint y hy).asIdeal.comap (Ideal.Quotient.mk V.affineIdeal)
  letI : Q.IsPrime := inferInstance
  have hQP : Q = P.comap (rationalPolynomialChartMap p0 p).toRingHom := by
    change (V.affinePointIdeal y).comap (Ideal.Quotient.mk V.affineIdeal) = _
    rw [V.affinePointIdeal_comap y hy]
    exact rationalPolynomialChartMap_point_kernel x p0 hp0 p
  let hI := projectiveRationalPolynomialChartMap_ideal f V hq hf hV x0 hx0
  let Φ := generalPointLocalQuotientPullback V.affineIdeal J P Q
    (rationalPolynomialChartMap p0 p).toRingHom hQP hI
  have hunram : Φ.FormallyUnramified :=
    generalPointLocalQuotientPullback_unramified_transport V.affineIdeal J
      (rationalPolynomialChartMap p0 p).toRingHom hI P P
      (P.comap (rationalPolynomialChartMap p0 p).toRingHom) Q rfl hQP.symm rfl hQP hu
  have hfinite := rationalPointLocalQuotientPullback_essFiniteType
    p0 p V.affineIdeal V.affineIdeal P Q hQP hI
  let L := V.affineIdeal.map (algebraMap _ (Localization.AtPrime Q))
  let M := J.map (algebraMap _ (Localization.AtPrime P))
  have hJP : J ≤ P := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro H hH
    change polynomialAwayPointEvaluation x p0 hp0
      (algebraMap _ (Localization.Away p0) H) = 0
    rw [polynomialAwayPointEvaluation_algebraMap]
    exact V.affineIdeal_le_pointKernel x hx hH
  have hM : M ≠ ⊤ := by
    have hle : M ≤ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono hJP
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hle
  letI : Nontrivial (Localization.AtPrime P ⧸ M) := Ideal.Quotient.nontrivial_iff.mpr hM
  letI : IsLocalRing (Localization.AtPrime P ⧸ M) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk M) Ideal.Quotient.mk_surjective
  obtain ⟨r, a, hr, ha⟩ := V.smoothPoint_polynomial_parameters hproper y hy ht
  have hg := general_point_local_unramified_parameters_generate V.affineIdeal J P Q
    (rationalPolynomialChartMap p0 p).toRingHom hQP hI hfinite hunram _ ha
  have hg' := hg.trans (point_local_quotient_maximalIdeal_map J P).symm
  refine ⟨x, hx, hp0, hy, hs, ht, ?_⟩
  unfold ProjectiveChartPolynomialParameterConclusion
  refine ⟨r, a, hr, ha, ?_⟩
  have he : (fun i => Φ (Ideal.Quotient.mk L
      (algebraMap _ (Localization.AtPrime Q) (a i)))) =
      (fun i => Ideal.Quotient.mk M (algebraMap _ (Localization.AtPrime P)
        (rationalPolynomialChartMap p0 p (a i)))) := by
    funext i
    exact generalPointLocalQuotientPullback_mk V.affineIdeal J P Q
      (rationalPolynomialChartMap p0 p).toRingHom hQP hI (a i)
  rw [he] at hg'
  exact hg'

end LinearStudy
