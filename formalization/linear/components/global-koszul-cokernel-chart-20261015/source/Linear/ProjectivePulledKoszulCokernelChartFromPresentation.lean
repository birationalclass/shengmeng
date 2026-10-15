module
public import Linear.NativeKoszulCokernelChartFromPresentation
public import Linear.ProjectivePulledLinearKoszulGlobal
public import Linear.HomogeneousQuotientKoszulAffineCounit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms
  nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  nativeProjectiveKoszulCokernelChartFromPresentationIso tildeKoszulPresentation
  tildeKoszulOriginalCutCokernelCofork
variable {n r : ℕ}

/-- For SAME ORIGINAL f,V,L,w,construct the actual original GLOBAL d1
cokernel on ANY original degree-one chart as the SAME affine original-cut
structure sheaf. ALL integer twists retained. Derive Noetherianity,generation
and original H degrees;no regularity,positive exactness,target comparison or
coefficient-module condition is assumed. Whole global finite-cut gluing
remains separate. The cofork point is proved to be actual i_*O_originalcut. -/
def projectivePulledLinearKoszulCokernelChartOriginalCutIso
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (a : CoordinateRing n ⧸ V.ideal.toIdeal) →
    (ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal 1) →
    let R := CommRingCat.of (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal) a)
    let j := Proj.awayι (homogeneousQuotientPiece V.ideal.toIdeal) a ha one_pos
    let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk
      (homogeneousQuotientPiece V.ideal.toIdeal) ha f.degree
      (projectivePulledLinearKoszulForms f V L w i)
      (by simpa using projectivePulledLinearKoszulForms_homogeneous f V L hL w i)
    (Scheme.Modules.restrictFunctor j).obj
      (cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0)) ≅
      (tildeKoszulOriginalCutCokernelCofork R h).pt := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  intro a ha
  unfold projectivePulledLinearKoszulComplex
  exact nativeProjectiveKoszulCokernelChartFromPresentationIso
    (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun i : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X i))
    (fun i => ⟨MvPolynomial.X i,MvPolynomial.isHomogeneous_X ℂ i,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k a ha

end LinearStudy