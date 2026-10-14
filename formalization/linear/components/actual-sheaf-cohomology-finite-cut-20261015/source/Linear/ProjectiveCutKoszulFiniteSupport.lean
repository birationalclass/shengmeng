module
public import Linear.ProjectiveCutKoszulQuotient
public import Linear.AffineFiniteCutSupport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] projectivePulledLinearSection_koszulQuotientAlgEquiv
variable {n r : ℕ}

/-- Transfer ORIGINAL finite cut coordinate ring to SAME ORIGINAL Koszul
quotient,through the already PROVED actual algebra equivalence. -/
theorem projectivePulledLinearSection_koszulQuotient_moduleFinite
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (hfin : Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸
      (projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K := ℂ)).toRingHom)) :
    Module.Finite ℂ ((MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) ⧸
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk V.affineIdeal
        (affineChartPolynomialMap
          (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))))) := by
  letI := hfin
  exact Module.Finite.equiv (projectivePulledLinearSection_koszulQuotientAlgEquiv f V L w).symm.toLinearEquiv

/-- SAME original closed Koszul cut has finite underlying spectrum,
derived from SAME original cut-ring finiteness;no abstract cut substitution. -/
theorem projectivePulledLinearSection_koszulCut_zeroLocus_finite
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (hfin : Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸
      (projectivePulledLinearSectionIdeal f V L w).map
        (affineChartPolynomialMap (K := ℂ)).toRingHom)) :
    (PrimeSpectrum.zeroLocus (Ideal.span (Set.range (fun i => Ideal.Quotient.mk V.affineIdeal
      (affineChartPolynomialMap
        (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))))) :
          Set (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal))).Finite := by
  letI := projectivePulledLinearSection_koszulQuotient_moduleFinite f V L w hfin
  exact affineClosedCut_zeroLocus_finite_of_fieldFinite ℂ _ _

end LinearStudy
