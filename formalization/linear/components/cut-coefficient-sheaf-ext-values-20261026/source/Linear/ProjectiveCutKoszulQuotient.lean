module
public import Linear.ProjectivePulledSectionAffineComparison
public import Linear.KoszulExactResolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- The degree-zero quotient of the original affine Koszul is canonically
the actual cut coordinate ring, preserving the original equations. -/
def projectivePulledLinearSection_koszulQuotientAlgEquiv
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ) :
    ((MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) ⧸
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk V.affineIdeal
        (affineChartPolynomialMap
          (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))))) ≃ₐ[ℂ]
      (MvPolynomial (Fin n) ℂ ⧸
        (projectivePulledLinearSectionIdeal f V L w).map
          (affineChartPolynomialMap (K := ℂ)).toRingHom) := by
  let J := Ideal.span (Set.range (fun i => affineChartPolynomialMap
    (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))))
  have hJ : J.map (Ideal.Quotient.mk V.affineIdeal)=
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk V.affineIdeal
        (affineChartPolynomialMap
          (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))))) := by
    dsimp only [J]
    rw [Ideal.map_span,← Set.range_comp']
  exact ((Ideal.quotientEquivAlgOfEq ℂ hJ.symm).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ ℂ V.affineIdeal J)).trans
      (Ideal.quotientEquivAlgOfEq ℂ (projectivePulledLinearSectionIdeal_map_affine f V L w).symm)

/-- Naturality on the actual polynomial classes fixes the identification
of the Koszul augmentation target with the whole original cut ring. -/
theorem projectivePulledLinearSection_koszulQuotientAlgEquiv_mk
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (w : Fin (r+1) → ℂ)
    (p : MvPolynomial (Fin n) ℂ) :
    projectivePulledLinearSection_koszulQuotientAlgEquiv f V L w
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk V.affineIdeal p))=
      Ideal.Quotient.mk _ p := by
  simp only [projectivePulledLinearSection_koszulQuotientAlgEquiv,AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk]
  rfl

end LinearStudy
