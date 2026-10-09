module
public import Linear.NativeProjectiveChartClosedPullback
public import Linear.ProjectiveAffineLinearSectionComparison
public import Mathlib.AlgebraicGeometry.Properties
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry
variable {n r : ℕ}

/-- The actual native closed linear-section ring is isomorphic to the
original affine equation quotient. Coordinate compatibility, extension of
the equation ideal and the third isomorphism theorem prove the comparison. -/
theorem projectiveNativeChartLinearSection_exists_quotient_equiv
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    Nonempty
      ((HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) ⧸
          projectiveNativeChartEquationIdeal V (fun _ : Fin r => 1)
            (projectiveLinearSectionForms L w) (projectiveLinearSectionForms_homogeneous L hL w)) ≃+*
        (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineLinearSectionIdeal V L w)) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let H := projectiveLinearSectionForms L w
  let hH := projectiveLinearSectionForms_homogeneous L hL w
  let K : Ideal (MvPolynomial (Fin n) ℂ) :=
    Ideal.span (Set.range (fun i => affineChartPolynomialMap (H i)))
  let K' := K.map (Ideal.Quotient.mk V.affineIdeal)
  let e := projectiveNativeChartRingEquiv V x hx
  let J := projectiveNativeChartEquationIdeal V (fun _ : Fin r => 1) H hH
  have he : K'.map e.toRingHom=J := by
    change (K.map (Ideal.Quotient.mk V.affineIdeal)).map e.toRingHom=J
    rw [Ideal.map_map,Ideal.map_span,← Set.range_comp']
    have hgen (i : Fin r) :
        e (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap (H i))) =
          projectiveNativeChartHomogeneousElement V 1 (H i) (hH i) :=
      projectiveNativeChartRingEquiv_homogeneous_mk V x hx 1 (H i) (hH i)
    change Ideal.span (Set.range (fun i : Fin r =>
      e (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap (H i))))) = J
    simp only [hgen]
    rfl
  exact ⟨(Ideal.quotientEquiv K' J e he.symm).symm.trans
    (DoubleQuot.quotQuotEquivQuotSup V.affineIdeal K)⟩

/-- Reducedness transfers through the proved actual native/affine closed
scheme ring comparison; point-set equality would not justify this step. -/
theorem projectiveNativeChartLinearSection_isReduced_of_affine
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ)
    (hrad : (projectiveAffineLinearSectionIdeal V L w).IsRadical) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    _root_.IsReduced
      (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) ⧸
          projectiveNativeChartEquationIdeal V (fun _ : Fin r => 1)
            (projectiveLinearSectionForms L w) (projectiveLinearSectionForms_homogeneous L hL w)) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : _root_.IsReduced (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineLinearSectionIdeal V L w) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp hrad
  obtain ⟨e⟩ := projectiveNativeChartLinearSection_exists_quotient_equiv V x hx L hL w
  exact isReduced_of_injective e.toRingHom e.injective

/-- The original finite linear normalization gives a nonempty target
open with reduced actual native chart zero schemes. Global Proj coverage
and the reducedness of their original-f pullbacks remain separate. -/
theorem projectiveNativeChartLinearSection_exists_reduced_schemes
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    ∃ c : MvPolynomial (Fin (r+1)) ℂ, c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
        w 0 ≠ 0 ∧ IsReduced (Spec (CommRingCat.of
          (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
            (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) ⧸
              projectiveNativeChartEquationIdeal V (fun _ : Fin r => 1)
                (projectiveLinearSectionForms L w) (projectiveLinearSectionForms_homogeneous L hL w)))) := by
  letI := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  obtain ⟨c,hc,hex,hgood⟩ := projective_linear_normalization_exists_affine_radical_sections
    V L hL hinj hfinite x hx
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨hw0,hrad,_⟩ := hgood w hw
  letI := projectiveNativeChartLinearSection_isReduced_of_affine V x hx L hL w hrad
  exact ⟨hw0,inferInstance⟩

end LinearStudy
