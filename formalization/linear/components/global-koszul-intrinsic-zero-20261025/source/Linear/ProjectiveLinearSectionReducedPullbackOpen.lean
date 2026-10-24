module
public import Linear.ProjectiveLinearSectionClosedReduced
public import Linear.ProjectiveGeneralReducedFibers
public import Linear.LinearProjectionSectionAvoidance
public import Linear.HomogeneousChartLift
public import Linear.NativeProjectiveChartSectionReduced
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r D : ℕ}

/-- Vanishing of a genuine homogeneous form at the actual normalized
projective point agrees with vanishing of its dehomogenization. -/
theorem normalizedProjectivePoint_homogeneous_vanish_iff
    (y : Fin n → ℂ) (H : CoordinateRing n) (hH : H.IsHomogeneous D) :
    MvPolynomial.eval (normalizedProjectivePoint y).rep H=0 ↔
      MvPolynomial.eval y (affineChartPolynomialMap H)=0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (Fin.cases 1 y : CoordinateVector n) (normalizedCoordinateVector_ne_zero y)
  change MvPolynomial.eval (Projectivization.mk ℂ (Fin.cases 1 y)
    (normalizedCoordinateVector_ne_zero y)).rep H=0 ↔ _
  rw [← ha,Units.smul_def,homogeneous_eval_smul hH]
  have he : MvPolynomial.eval (Fin.cases 1 y) H =
      MvPolynomial.eval y (affineChartPolynomialMap H) :=
    (AlgHom.congr_fun (affineChartPolynomialMap_comp_aeval (K := ℂ) y) H).symm
  rw [he]
  simp [pow_ne_zero D a.isUnit.ne_zero]

/-- A normalized point satisfying the ORIGINAL affine section equations
belongs to that very projective linear section, including rep scaling. -/
theorem normalizedProjectivePoint_mem_linearSection
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1) (w : Fin (r+1) → ℂ)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (heq : ∀ i, MvPolynomial.eval y
      (affineChartPolynomialMap (projectiveLinearSectionForms L w i))=0) :
    normalizedProjectivePoint y ∈ projectiveLinearSection V L w := by
  apply (projective_linear_section_defining_forms_iff V L w _).mpr
  exact ⟨hy,fun i => (normalizedProjectivePoint_homogeneous_vanish_iff y _
    (projectiveLinearSectionForms_homogeneous L hL w i)).mpr (heq i)⟩

/-- For the SAME original finite linear normalization, construct a
nonempty target open on which the EXACT substituted original-f equation
ideal in the source denominator chart is radical. Both target-section
reducedness and ALL individual fiber reducedness are DERIVED, not inputs.
This remains a first-chart result, not global Proj coverage. -/
theorem projectiveLinearSection_exists_reduced_pullback_open
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
        w 0 ≠ 0 ∧ (projectiveAffineLinearSectionIdeal V L w).IsRadical ∧
          Module.Finite ℂ
            (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineLinearSectionIdeal V L w) ∧
          (projectiveNativeChartPullbackEquationIdeal f V
            (projectiveLinearSectionForms L w)).IsRadical := by
  obtain ⟨a,ha,_,htarget⟩ := projective_linear_normalization_exists_affine_radical_sections
    V L hL hinj hfinite x0 hx0
  obtain ⟨p,hp,_,_,hgood⟩ := projective_exists_general_whole_reduced_fibers
    f V hq hf hV x0 hx0
  obtain ⟨D,H,hHom,hH,hchart⟩ := projective_exists_homogeneous_chart_avoidance V x0 hx0 p hp
  obtain ⟨b,hb,havoid⟩ := finite_linear_projection_exists_projective_section_avoiding
    V L hL hfinite H hHom hH
  have hc : a*b ≠ 0 := mul_ne_zero ha hb
  have hex : ∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w (a*b) ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    exact h w
  refine ⟨a*b,hc,hex,?_⟩
  intro w hw
  rw [map_mul] at hw
  obtain ⟨hwa,hwb⟩ := mul_ne_zero_iff.mp hw
  obtain ⟨hw0,hrad,hfin⟩ := htarget w hwa
  letI := hfin
  have hfib (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
      (heq : ∀ i, MvPolynomial.eval y
        (affineChartPolynomialMap (projectiveLinearSectionForms L w i))=0) :
      _root_.IsReduced (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) := by
    have hz := normalizedProjectivePoint_mem_linearSection V L hL w y hy heq
    have havoidH := havoid w hw0 hwb (normalizedProjectivePoint y) hz
    have hdehom : MvPolynomial.eval y (affineChartPolynomialMap H) ≠ 0 := by
      intro hzero
      exact havoidH ((normalizedProjectivePoint_homogeneous_vanish_iff y H hHom).mpr hzero)
    have hraw : MvPolynomial.eval (Fin.cases 1 y) H ≠ 0 := by
      intro hzero
      exact hdehom ((AlgHom.congr_fun (affineChartPolynomialMap_comp_aeval (K := ℂ) y) H).trans hzero)
    have hyp : MvPolynomial.eval y p ≠ 0 := by
      simpa using (hchart (Fin.cases 1 y) hraw).2
    exact (hgood y hy hyp).2.2.2.1
  have hradPull := projectiveChartLinearSection_map_isRadical_of_reduced_fibers
    f V hq hf hV x0 hx0 L w hrad hfib
  have hid := projectiveChartLinearSection_map_eq_pulled_equationIdeal
    f V hq hf hV x0 hx0 L hL w
  exact ⟨hw0,hrad,hfin,hid ▸ hradPull⟩

/-- The actually pulled common-zero SCHEME in the original denominator
chart is reduced on a constructed nonempty open. Its defining ideal is
unchanged; no radicalization or assumed reduced source scheme is used. -/
theorem projectiveLinearSection_exists_reduced_pulled_schemes
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
        w 0 ≠ 0 ∧ AlgebraicGeometry.IsReduced
          (AlgebraicGeometry.Spec (CommRingCat.of
            (Localization.Away (projectiveChartDenominator f V) ⧸
              projectiveNativeChartPullbackEquationIdeal f V (projectiveLinearSectionForms L w)))) := by
  obtain ⟨c,hc,hex,hgood⟩ := projectiveLinearSection_exists_reduced_pullback_open
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,_,_,hrad⟩ := hgood w hw
  letI := (Ideal.isRadical_iff_quotient_reduced _).mp hrad
  exact ⟨hw0,inferInstance⟩

end LinearStudy
