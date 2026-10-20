module
public import Linear.LinearNormalizationBasePoint
public import Linear.ProjectiveConeHilbertKrullDimension
public import Linear.ProjectiveChartHilbertKrullDimension
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual map defined by the chosen original linear forms. -/
def projectiveLinearNormalizationMap {n r : ℕ}
    (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) :
    MvPolynomial (Fin (r+1)) ℂ →ₐ[ℂ] (CoordinateRing n ⧸ V.ideal.toIdeal) :=
  (Ideal.Quotient.mkₐ ℂ V.ideal.toIdeal).comp (MvPolynomial.aeval L)

/-- Construct actual linear forms for the original projective variety,
not only an abstract finite map. Their cone map is injective and finite
and has no base point on V. The same actual Hilbert degree r determines
the number r+1 of forms. Exact generic section cardinality is NOT claimed. -/
theorem projective_exists_linear_normalization {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    ∃ (r : ℕ) (P : Polynomial ℚ), r ≤ n ∧ P ≠ 0 ∧ P.natDegree = r ∧
      (∃ N : ℕ, ∀ m > N, P.eval (m : ℚ) =
        (homogeneousQuotientHilbert V.ideal.toIdeal m : ℚ)) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i, (L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        ringKrullDim (CoordinateRing n ⧸ V.ideal.toIdeal) = ((r+1 : ℕ) : WithBot ℕ∞) ∧
        ∀ (v : CoordinateVector n), v ≠ 0 →
          (∀ H ∈ V.ideal.toIdeal, MvPolynomial.eval v H = 0) →
          (fun i => MvPolynomial.eval v (L i)) ≠ 0 := by
  classical
  obtain ⟨P,hP,hpn,hcone,hHilbert⟩ := projective_cone_hilbertPolynomial_krull_dimension V
  obtain ⟨s,hs,g,hinj,hfinite,hdim,hlinear⟩ :=
    exists_linear_finite_normalization_krull_dimension V.ideal.toIdeal
      V.prime.ne_top V.ideal.isHomogeneous
  have hsEq : s = P.natDegree+1 := by
    have h : (s : WithBot ℕ∞) = ((P.natDegree+1 : ℕ) : WithBot ℕ∞) :=
      hdim.symm.trans hcone
    exact_mod_cast h
  subst s
  choose L hL hg using hlinear
  have heq : projectiveLinearNormalizationMap V L = g := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [projectiveLinearNormalizationMap,AlgHom.comp_apply,
      MvPolynomial.aeval_X,Ideal.Quotient.mkₐ_eq_mk] using (hg i).symm
  refine ⟨P.natDegree,P,hpn,hP,rfl,hHilbert,L,hL,heq ▸ hinj,heq ▸ hfinite,hcone,?_⟩
  intro v hv hV hzero
  have hLv (i) : MvPolynomial.eval v (L i) = 0 := congrFun hzero i
  have hvI : v ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal := by
    intro H hH
    simpa only [MvPolynomial.aeval_eq_eval] using hV H hH
  exact hv (integral_linear_normalization_origin_zeroLocus V.ideal.toIdeal
    V.ideal.isHomogeneous L hL g hg hfinite.to_isIntegral v hvI hLv)

/-- The constructed projection's r is also the ACTUAL original affine
chart's Krull dimension. An existing original point suffices to make
the cone/chart comparison; no new dimension is supplied as an input. -/
theorem projective_exists_linear_normalization_chart_dimension {n : ℕ}
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i, (L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        ∀ (v : CoordinateVector n), v ≠ 0 →
          (∀ H ∈ V.ideal.toIdeal, MvPolynomial.eval v H = 0) →
          (fun i => MvPolynomial.eval v (L i)) ≠ 0 := by
  obtain ⟨r,P,hrn,hP,hdegree,hHilbert,L,hL,hinj,hfinite,hdim,hfree⟩ :=
    projective_exists_linear_normalization V
  have hchart := projective_chart_krull_dimension_of_hilbertPolynomial V x hx P hP hHilbert
  rw [hdegree] at hchart
  exact ⟨r,hrn,hchart,L,hL,hinj,hfinite,hfree⟩

end LinearStudy
