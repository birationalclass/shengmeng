module
public import Linear.HomogeneousQuotientNativeChart
public import Linear.ProjectivePulledSectionAffineComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open AlgebraicGeometry CategoryTheory
variable {n r : ℕ}

/-- WHOLE Proj of the actual homogeneous cut is its actual dehomogenized
affine quotient when the cut avoids X0=0. No integrality or reducedness
assumption is introduced in this comparison. -/
theorem homogeneousCut_exists_actual_affine_scheme_iso
    (I : Ideal (CoordinateRing n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℂ))
    (havoid : ∀ v : CoordinateVector n, v ∈ MvPolynomial.zeroLocus ℂ I →
      v 0=0 → v=0) :
    letI := homogeneousQuotientGrading I hI
    Nonempty (Proj (homogeneousQuotientPiece I) ≅
      Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸
        I.map (affineChartPolynomialMap (K := ℂ)).toRingHom))) := by
  letI := homogeneousQuotientGrading I hI
  obtain ⟨ec,_⟩ := homogeneousQuotient_nativeChart_ringEquiv I hI
  obtain ⟨es⟩ := homogeneousCut_exists_native_chart_scheme_iso I hI
    (MvPolynomial.X 0) 1 (MvPolynomial.isHomogeneous_X ℂ 0) Nat.zero_lt_one
    (fun v hv hz => havoid v hv (by simpa using hz))
  exact ⟨es.trans (Scheme.Spec.mapIso ec.toCommRingCatIso.op)⟩

/-- The actual pulled section as mathlib's native Proj of its ORIGINAL
homogeneous quotient. The ideal is not replaced by its radical. -/
def projectivePulledLinearSectionScheme
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) : Scheme := by
  let I := projectivePulledLinearSectionIdeal f V L w
  letI := homogeneousQuotientGrading I (projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w)
  exact Proj (homogeneousQuotientPiece I)

/-- A nonempty open constructed from ORIGINAL f,V and the SAME finite
linear normalization gives WHOLE native pulled section schemes that are
reduced and isomorphic to spectra of the actual finite affine cut algebras.
Neither coverage, native chart comparison nor source reducedness is assumed. -/
theorem projectivePulledLinearSection_exists_global_finite_reduced_schemes
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
        let C := MvPolynomial (Fin n) ℂ ⧸
          (projectivePulledLinearSectionIdeal f V L w).map (affineChartPolynomialMap (K := ℂ)).toRingHom
        w 0 ≠ 0 ∧ _root_.IsReduced C ∧ Module.Finite ℂ C ∧
          Nonempty (projectivePulledLinearSectionScheme f V L hL w ≅ Spec (CommRingCat.of C)) ∧
          AlgebraicGeometry.IsReduced (projectivePulledLinearSectionScheme f V L hL w) := by
  obtain ⟨c,hc,hex,hgood⟩ := projectivePulledLinearSection_exists_chart_avoidance_open
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hred,hfin,havoid⟩ := hgood w hw
  let A := Localization.Away (projectiveChartDenominator f V) ⧸
    projectiveNativeChartPullbackEquationIdeal f V (projectiveLinearSectionForms L w)
  let C := MvPolynomial (Fin n) ℂ ⧸
    (projectivePulledLinearSectionIdeal f V L w).map (affineChartPolynomialMap (K := ℂ)).toRingHom
  letI : _root_.IsReduced A := hred
  letI : Module.Finite ℂ A := hfin
  obtain ⟨e⟩ := projectivePulledLinearSection_affine_exists_quotient_algEquiv f V L w
    (fun v hv hvne => (havoid v hv hvne).2)
  letI : _root_.IsReduced C := isReduced_of_injective e.toRingHom e.injective
  letI : Module.Finite ℂ C := Module.Finite.of_injective e.toLinearMap e.injective
  obtain ⟨es⟩ := homogeneousCut_exists_actual_affine_scheme_iso
    (projectivePulledLinearSectionIdeal f V L w)
    (projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w)
    (fun v hv hz => by
      by_contra hvne
      exact (havoid v hv hvne).1 hz)
  have hscheme : AlgebraicGeometry.IsReduced (projectivePulledLinearSectionScheme f V L hL w) :=
    AlgebraicGeometry.isReduced_of_isOpenImmersion es.hom
  exact ⟨hw0,inferInstance,inferInstance,⟨es⟩,hscheme⟩

end LinearStudy
