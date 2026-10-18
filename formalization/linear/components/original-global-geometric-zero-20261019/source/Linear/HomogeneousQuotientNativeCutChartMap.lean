module
public import Linear.ProjectivePulledSectionClosedEmbedding
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K] {n : ℕ}

/-- The ACTUAL original graded quotient-factor map sends each original
homogeneous fraction H/X0^m to the SAME polynomial fraction in the
original cut quotient. Ideals and nilpotents are retained. -/
theorem homogeneousQuotientFactor_away_originalFraction
    (I J : Ideal (MvPolynomial (Fin (n+1)) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ K))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ K)) (hIJ : I ≤ J)
    (m : ℕ) (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous m) :
    letI := homogeneousQuotientGrading I hI
    letI := homogeneousQuotientGrading J hJ
    let φ := homogeneousQuotientFactorGraded I J hIJ
    Away.map φ (Ideal.Quotient.mk I (MvPolynomial.X 0))
      (homogeneousQuotientNativeChartElement I hI m H hH) =
        homogeneousQuotientNativeChartElement J hJ m H hH := by
  letI := homogeneousQuotientGrading I hI
  letI := homogeneousQuotientGrading J hJ
  dsimp only
  unfold homogeneousQuotientNativeChartElement
  rw [Away.map_mk]
  rfl

/-- The SAME original homogeneous quotient closed embedding commutes
with the ACTUAL native first-chart maps via the SAME original quotient
away-ring map. Reuse mathlib Proj.awayι_comp_map;no arbitrary scheme iso
or desired diagram-compatibility certificate is assumed. -/
theorem homogeneousQuotientClosedEmbedding_away_square
    (I J : Ideal (MvPolynomial (Fin (n+1)) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ K))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ K)) (hIJ : I ≤ J) :
    letI := homogeneousQuotientGrading I hI
    letI := homogeneousQuotientGrading J hJ
    let φ := homogeneousQuotientFactorGraded I J hIJ
    let a := Ideal.Quotient.mk I (MvPolynomial.X 0)
    let ha : a ∈ homogeneousQuotientPiece I 1 :=
      ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X K 0,rfl⟩
    Proj.awayι (homogeneousQuotientPiece J) (φ a) (φ.map_mem ha) one_pos ≫
        homogeneousQuotientClosedEmbedding I J hI hJ hIJ =
      Spec.map (CommRingCat.ofHom (Away.map φ a)) ≫
        Proj.awayι (homogeneousQuotientPiece I) a ha one_pos := by
  letI := homogeneousQuotientGrading I hI
  letI := homogeneousQuotientGrading J hJ
  exact Proj.awayι_comp_map (homogeneousQuotientFactorGraded I J hIJ)
    (graded_surjective_irrelevant_le_map _ (homogeneousQuotientFactorGraded_surjective I J hIJ))
    one_pos (Ideal.Quotient.mk I (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X K 0,rfl⟩

end LinearStudy
