module
public import Linear.ProjectivePulledOriginalKoszulTopBoundary
public import Linear.SchemeModuleOriginalExtOpenRestriction
public import Linear.ProjectivePulledOriginalChainWholeCutExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf projectivePulledLinearKoszulForms
  projectivePulledLinearKoszulComplex projectivePulledWholeCutResolutionTarget
  projectivePulledKoszulTopResolutionTarget
variable {n r : ℕ}

/-- ACTUAL original X0-chart restriction of the SAME original whole-cut
global derived Ext class. Native open restriction sends it to the ACTUAL
restricted cochain-resolution roof,with its SAME cocycle and augmentation.
All exactness/additivity/Ext/derived-category prerequisites are constructed.
The original Setup family supplies e and he. Identification with affine
MODULE Ext,internal SHEAF Ext and connecting homomorphisms stays separate. -/
def projectivePulledOriginalWholeCutExtChartRestrictionProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k)
    (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      QuasiIso (originalChainCokernelTargetAugmentation
        (projectivePulledLinearKoszulComplex f V L hL w k)
        (projectivePulledWholeCutResolutionTarget f V L hL w k) e)) :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let j := Proj.awayι (m := 1) (homogeneousQuotientPiece V.ideal.toIdeal)
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩ one_pos
  letI : IsOpenImmersion j := by
    dsimp only [j,Proj.awayι]
    exact IsOpenImmersion.comp _ _
  schemeModuleOriginalChainTopExtOpenRestrictionProof j
    (projectivePulledLinearKoszulComplex f V L hL w k) r
    (originalChainCokernelTargetAugmentation (projectivePulledLinearKoszulComplex f V L hL w k)
      (projectivePulledWholeCutResolutionTarget f V L hL w k) e) he
    (projectivePulledOriginalKoszulTopTwistIso f V L hL w k).hom
    (projectivePulledOriginalKoszulTopFunctional_isCocycle f V L hL w k _)

end LinearStudy
