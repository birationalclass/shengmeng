module
public import Linear.GradedSurjectiveProjClosed
public import Linear.ProjectivePulledSectionGlobalReduced
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
open AlgebraicGeometry CategoryTheory
variable {n r : ℕ}

/-- The actual quotient factor map, bundled as a graded map.
Its degree pieces are the original homogeneous polynomial images. -/
def homogeneousQuotientFactorGraded {K ι : Type*} [Field K]
    (I J : Ideal (MvPolynomial ι K)) (hIJ : I ≤ J) :
    homogeneousQuotientPiece I →+*ᵍ homogeneousQuotientPiece J where
  __ := Ideal.Quotient.factor hIJ
  map_mem := by
    intro m a ha
    obtain ⟨H,hH,rfl⟩ := (homogeneousQuotientPiece_mem_iff I m a).mp ha
    exact ⟨H,hH,Ideal.Quotient.factor_mk hIJ H⟩

theorem homogeneousQuotientFactorGraded_surjective {K ι : Type*} [Field K]
    (I J : Ideal (MvPolynomial ι K)) (hIJ : I ≤ J) :
    Function.Surjective (homogeneousQuotientFactorGraded I J hIJ) :=
  Ideal.Quotient.factor_surjective hIJ

/-- Natural closed embedding from the original homogeneous quotient J
into the original homogeneous quotient I. No radicalization, chart
choice or reducedness hypothesis is involved. -/
def homogeneousQuotientClosedEmbedding {K ι : Type*} [Field K]
    (I J : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K)) (hIJ : I ≤ J) :
    letI := homogeneousQuotientGrading I hI
    letI := homogeneousQuotientGrading J hJ
    Proj (homogeneousQuotientPiece J) ⟶ Proj (homogeneousQuotientPiece I) := by
  letI := homogeneousQuotientGrading I hI
  letI := homogeneousQuotientGrading J hJ
  exact Proj.map (homogeneousQuotientFactorGraded I J hIJ)
    (graded_surjective_irrelevant_le_map _ (homogeneousQuotientFactorGraded_surjective I J hIJ))

theorem homogeneousQuotientClosedEmbedding_isClosedImmersion {K ι : Type*} [Field K]
    (I J : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K)) (hIJ : I ≤ J) :
    letI := homogeneousQuotientGrading I hI
    letI := homogeneousQuotientGrading J hJ
    IsClosedImmersion (homogeneousQuotientClosedEmbedding I J hI hJ hIJ) := by
  letI := homogeneousQuotientGrading I hI
  letI := homogeneousQuotientGrading J hJ
  exact graded_surjective_Proj_map_closedImmersion _
    (homogeneousQuotientFactorGraded_surjective I J hIJ)

/-- The actual pulled section's natural closed embedding into original
V: the map is induced by the SAME original homogeneous ideal inclusion. -/
def projectivePulledLinearSectionClosedEmbedding
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    projectivePulledLinearSectionScheme f V L hL w ⟶ Proj (homogeneousQuotientPiece V.ideal.toIdeal) :=
  homogeneousQuotientClosedEmbedding V.ideal.toIdeal
    (projectivePulledLinearSectionIdeal f V L w) V.ideal.isHomogeneous
    (projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w) le_sup_left

theorem projectivePulledLinearSectionClosedEmbedding_isClosedImmersion
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    IsClosedImmersion (projectivePulledLinearSectionClosedEmbedding f V L hL w) :=
  homogeneousQuotientClosedEmbedding_isClosedImmersion V.ideal.toIdeal
    (projectivePulledLinearSectionIdeal f V L w) V.ideal.isHomogeneous
    (projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w) le_sup_left

end LinearStudy
