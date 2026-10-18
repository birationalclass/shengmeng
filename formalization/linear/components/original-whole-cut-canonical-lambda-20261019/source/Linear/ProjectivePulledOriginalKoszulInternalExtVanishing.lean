module
public import Linear.HomogeneousQuotientKoszulTermInternalExtVanishing
public import Linear.ProjectivePulledLinearKoszulGlobal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf projectivePulledLinearKoszulForms
variable {n r : ℕ}

/-- The SAME NAMED ORIGINAL global Koszul complex used by the original
whole-cut augmentation has acyclic source terms for INTERNAL SHEAF Ext.
ALL original f,V,L,w,ALL integerk,ALL p and ANY coefficient N. No new
source acyclicity/coordinate-cover premise is supplied. -/
theorem projectivePulledOriginalKoszulInternalExt_succ
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) (p : ℕ)
    (N : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      (AlgebraicGeometry.Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules) (q : ℕ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    IsZero (schemeModuleInternalExt
      ((projectivePulledLinearKoszulComplex f V L hL w k).X p) N (q+1)) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  change IsZero (schemeModuleInternalExt
    ((nativeProjectiveKoszulComplex (homogeneousQuotientPiece V.ideal.toIdeal)
      (projectivePulledLinearKoszulForms f V L w)
      (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k).X p) N (q+1))
  rw [nativeProjectiveKoszulComplex_X]
  exact homogeneousQuotientKoszulTermInternalExt_succ V.ideal.toIdeal
    V.ideal.isHomogeneous r f.degree p k N q

end LinearStudy
