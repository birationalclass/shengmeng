module
public import Linear.NativeKoszulZeroTermTwistIso
public import Linear.ProjectivePulledOriginalKoszulTopBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf projectivePulledLinearKoszulForms
  projectivePulledKoszulTopResolutionTarget
variable {n r : ℕ}
/-- The SAME original degree-zero Koszul term is the SAME native O_V(k),
using its actual empty exterior basis,not a supplied comparison. -/
def projectivePulledOriginalKoszulZeroTwistIso
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (projectivePulledLinearKoszulComplex f V L hL w k).X 0 ≅
      nativeProjectiveModuleSheaf (homogeneousQuotientPiece V.ideal.toIdeal)
        (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal))
        (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece V.ideal.toIdeal)) k := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact nativeProjectiveKoszulComplexZeroTwistIso (homogeneousQuotientPiece V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k
/-- At the ORIGINAL t=r*q-r-1,the actual original top term is exactly
native O_V(-r-1). Both the exterior-basis map and original numerical
coefficient identity are proved;no coefficient identification is assumed. -/
def projectivePulledOriginalKoszulTopOriginalCoefficientIso
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)).X r ≅
      nativeProjectiveModuleSheaf (homogeneousQuotientPiece V.ideal.toIdeal)
        (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal))
        (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece V.ideal.toIdeal)) (-(r : ℤ)-1) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact projectivePulledOriginalKoszulTopTwistIso f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1) ≪≫
    eqToIso (projectivePulledKoszulTopResolutionTarget_original_t f V r)
end LinearStudy
