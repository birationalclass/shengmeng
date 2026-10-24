module
public import Linear.HomogeneousCutChartCoverage
public import Linear.ProjectiveLinearSectionFinitePullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open AlgebraicGeometry CategoryTheory
variable {n r : ℕ}

/-- The ACTUAL homogeneous ideal defining the original pulled linear
section, with its original substituted equations and nilpotents retained. -/
def projectivePulledLinearSectionIdeal
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) : Ideal (CoordinateRing n) :=
  V.ideal.toIdeal ⊔ Ideal.span (Set.range (fun i =>
    MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))

theorem projectivePulledLinearSectionIdeal_isHomogeneous
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) :
    (projectivePulledLinearSectionIdeal f V L w).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule _ ℂ) := by
  apply V.ideal.isHomogeneous.sup
  apply Ideal.homogeneous_span
  rintro _ ⟨i,rfl⟩
  exact ⟨f.degree,projective_pulled_back_section_forms_homogeneous f L hL w i⟩

/-- Original good whole fibers and original section avoidance derive
that the ENTIRE actual cone cut has no nonzero point on X0=0 or f0=0.
The SAME open also retains the proved finite reduced denominator quotient. -/
theorem projectivePulledLinearSection_exists_chart_avoidance_open
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
          _root_.IsReduced (Localization.Away (projectiveChartDenominator f V) ⧸
            projectiveNativeChartPullbackEquationIdeal f V (projectiveLinearSectionForms L w)) ∧
          Module.Finite ℂ (Localization.Away (projectiveChartDenominator f V) ⧸
            projectiveNativeChartPullbackEquationIdeal f V (projectiveLinearSectionForms L w)) ∧
          ∀ v : CoordinateVector n,
            v ∈ MvPolynomial.zeroLocus ℂ (projectivePulledLinearSectionIdeal f V L w) →
              v ≠ 0 → v 0 ≠ 0 ∧ MvPolynomial.eval v (f.forms 0) ≠ 0 := by
  obtain ⟨a,ha,_,hfiniteRed⟩ := projectiveLinearSection_exists_finite_reduced_pullbacks
    f V hq hf hV L hL hinj hfinite x0 hx0
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
  obtain ⟨hw0,hred,hfin⟩ := hfiniteRed w hwa
  refine ⟨hw0,hred,hfin,?_⟩
  intro v hv hvne
  have hvI : v ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal :=
    fun F hF => hv F (Ideal.mem_sup_left hF)
  have hvH (i : Fin r) :
      MvPolynomial.eval v (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))=0 :=
    hv _ (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i)))
  let x := Projectivization.mk ℂ v hvne
  let z := f.onPoints x
  obtain ⟨u,hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hvne
  have hxH (i : Fin r) :
      MvPolynomial.eval x.rep (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))=0 := by
    change MvPolynomial.eval (Projectivization.mk ℂ v hvne).rep _=0
    rw [← hu,Units.smul_def,homogeneous_eval_smul
      (projective_pulled_back_section_forms_homogeneous f L hL w i),hvH i,mul_zero]
  have hsect : z ∈ projectiveLinearSection V L w := by
    have he := projective_pulled_back_section_common_points f V hV L hL w
    have hxmem : x ∈ {x : ProjectivePoint n | x ∈ V.zeroSet ∧ ∀ i,
      MvPolynomial.eval x.rep (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))=0} :=
      ⟨(V.mem_zeroSet_mk v hvne).mpr hvI,hxH⟩
    rw [he] at hxmem
    exact hxmem
  obtain ⟨hz0,hyp⟩ := hchart z.rep (havoid w hw0 hwb z hsect)
  let y : Fin n → ℂ := fun i => z.rep i.succ/z.rep 0
  have hy : normalizedProjectivePoint y ∈ V.zeroSet :=
    V.normalizedConePoint_mem z.rep hsect.1 hz0
  have hzy : normalizedProjectivePoint y=z := by
    exact (normalizedProjectivePoint_coordinate_ratios z.rep (Projectivization.rep_nonzero z) hz0).trans
      (Projectivization.mk_rep z)
  have hfv : f.onPoints (Projectivization.mk ℂ v hvne)=normalizedProjectivePoint y := hzy.symm
  have hv0 := (hgood y hy hyp).2.1 v hvne hfv
  have hf0 : MvPolynomial.eval v (f.forms 0) ≠ 0 := by
    intro hzero
    have hzmk : z=Projectivization.mk ℂ (f.evalVector v) (f.noBasePoint v hvne) :=
      f.onPoints_mk v hvne
    obtain ⟨u',hu'⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
      (f.evalVector v) (f.noBasePoint v hvne)
    apply hz0
    rw [hzmk,← hu',Units.smul_def]
    change (u' : ℂ)*MvPolynomial.eval v (f.forms 0)=0
    rw [hzero,mul_zero]
  exact ⟨hv0,hf0⟩

/-- Every native Proj prime of the ACTUAL pulled cut lies in BOTH
the X0 and f0 basic opens. Closed-point avoidance is upgraded to full
scheme-open coverage by Nullstellensatz; no global coverage is assumed. -/
theorem projectivePulledLinearSection_exists_native_open_coverage
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
        let I := projectivePulledLinearSectionIdeal f V L w
        letI := homogeneousQuotientGrading I (projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w)
        Proj.basicOpen (homogeneousQuotientPiece I) (Ideal.Quotient.mk I (MvPolynomial.X 0))=⊤ ∧
          Proj.basicOpen (homogeneousQuotientPiece I) (Ideal.Quotient.mk I (f.forms 0))=⊤ := by
  obtain ⟨c,hc,hex,hgood⟩ := projectivePulledLinearSection_exists_chart_avoidance_open
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨_,_,_,havoid⟩ := hgood w hw
  let I := projectivePulledLinearSectionIdeal f V L w
  let hI := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
  letI := homogeneousQuotientGrading I hI
  constructor
  · apply homogeneousCut_basicOpen_eq_top_of_point_avoidance I hI (MvPolynomial.X 0)
    intro v hv hz
    by_contra hvne
    exact (havoid v hv hvne).1 (by simpa using hz)
  · apply homogeneousCut_basicOpen_eq_top_of_point_avoidance I hI (f.forms 0)
    intro v hv hz
    by_contra hvne
    exact (havoid v hv hvne).2 hz

end LinearStudy
