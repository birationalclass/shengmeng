module
public import Linear.ProjectivePulledSectionClosedEmbedding
public import Linear.NativeIntegerTwistWholeChartFrame
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveModuleSheaf
variable {n r : ℕ}

/-- The ACTUAL original whole-cut native twist pushed along its ORIGINAL
homogeneous quotient closed embedding. This is a constructed object,not
an assumed target comparison or a proof of source exactness. -/
def projectivePulledWholeCutResolutionTarget (f : HomogeneousEndomorphism n)
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i,(L i).IsHomogeneous 1) (w : Fin (r+1) → ℂ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules := by
  let J := projectivePulledLinearSectionIdeal f V L w
  let hJ := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := homogeneousQuotientGrading J hJ
  exact (Scheme.Modules.pushforward (projectivePulledLinearSectionClosedEmbedding f V L hL w)).obj
    (nativeProjectiveModuleSheaf (homogeneousQuotientPiece J)
      (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece J))
      (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece J)) k)

/-- The ACTUAL coefficient twist for the original top Koszul term.
At the manuscript's t=r*q-r-1,this is native O_V(-r-1),independent of f. -/
def projectivePulledKoszulTopResolutionTarget (f : HomogeneousEndomorphism n)
    (V : IntegralProjectiveEquations n) (rank : ℕ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact nativeProjectiveModuleSheaf (homogeneousQuotientPiece V.ideal.toIdeal)
    (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal))
    (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece V.ideal.toIdeal))
    (k-(rank:ℤ)*(f.degree:ℤ))

/-- Verify the original numerical choice of t in the ACTUAL native
coefficient sheaf. This does not yet identify an ambient pullback twist. -/
theorem projectivePulledKoszulTopResolutionTarget_original_t
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (rank : ℕ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    projectivePulledKoszulTopResolutionTarget f V rank
      ((rank:ℤ)*(f.degree:ℤ)-(rank:ℤ)-1) =
      nativeProjectiveModuleSheaf (homogeneousQuotientPiece V.ideal.toIdeal)
        (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal))
        (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece V.ideal.toIdeal))
        (-(rank:ℤ)-1) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  unfold projectivePulledKoszulTopResolutionTarget
  congr 1
  omega

end LinearStudy
