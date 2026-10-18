module
public import Linear.ProjectivePulledWholeCutResolutionObjects
public import Linear.ProjectivePulledLinearKoszulGlobal
public import Linear.NativeKoszulFiniteTopTerm
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf projectivePulledLinearKoszulForms
variable {n r : ℕ}

/-- Identify the ACTUAL top term of the SAME ORIGINAL named complex.
The native full exterior-basis isomorphism is constructed, not supplied.
Keep the original complex as source for subsequent augmentation/Ext maps. -/
def projectivePulledOriginalKoszulTopTwistIso
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (projectivePulledLinearKoszulComplex f V L hL w k).X r ≅
      projectivePulledKoszulTopResolutionTarget f V r k := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact nativeProjectiveKoszulComplexTopTwistIso (homogeneousQuotientPiece V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k

/-- Every actual top functional on the SAME original complex is a cocycle.
The next term vanishes by the actual exterior basis; no exactness input. -/
theorem projectivePulledOriginalKoszulTopFunctional_isCocycle
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    ∀ {M : (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules}
      (a : (projectivePulledLinearKoszulComplex f V L hL w k).X r ⟶ M),
      (projectivePulledLinearKoszulComplex f V L hL w k).d (r+1) r ≫ a = 0 := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  intro M a
  exact nativeProjectiveKoszulGlobalTopFunctional_isCocycle
    (homogeneousQuotientPiece V.ideal.toIdeal) (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k a

end LinearStudy
