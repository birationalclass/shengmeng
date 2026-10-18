module
public import Linear.HomogeneousQuotientKoszulAffineStandard
public import Linear.ProjectivePulledLinearKoszulForms
import all Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulTerm
  nativeProjectiveKoszulOnAffine nativeProjectiveKoszulComplex projectivePulledLinearKoszulForms
  homogeneousQuotientKoszulStandardAffineIso nativeProjectiveKoszulStandardAffineIso
variable {n r : ℕ}

/-- SAME ORIGINAL f,V,L,w global pulled-linear Koszul,restricted to ANY
original positive coordinate chart,equals the native standard exterior
Koszul on the SAME original H_i/a^q. Homogeneity,Noetherianity,sourceQC and
all chart/differential compatibility are DERIVED;no such certificate input. -/
def projectivePulledLinearKoszulStandardAffineIso
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (a : CoordinateRing n ⧸ V.ideal.toIdeal) →
    (ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal 1) →
    let R := CommRingCat.of (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal) a)
    let j := Proj.awayι (homogeneousQuotientPiece V.ideal.toIdeal) a ha one_pos
    letI : (tilde.functor R).Additive :=
      AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor (R := R)
    nativeProjectiveKoszulOnAffine (homogeneousQuotientPiece V.ideal.toIdeal) R j
      (projectivePulledLinearKoszulForms f V L w)
      (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k ≅
    ((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (koszulComplex (Fintype.linearCombination
        (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal) a)
        (fun i => HomogeneousLocalization.Away.mk (homogeneousQuotientPiece V.ideal.toIdeal)
          ha f.degree (projectivePulledLinearKoszulForms f V L w i)
          (by simpa using projectivePulledLinearKoszulForms_homogeneous f V L hL w i)))) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  intro a ha
  exact homogeneousQuotientKoszulStandardAffineIso V.ideal.toIdeal V.ideal.isHomogeneous
    (projectivePulledLinearKoszulForms f V L w) k
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) a ha

end LinearStudy
