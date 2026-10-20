module
public import Linear.ProjectivePulledOriginalFixedTopActualSectionSequence
public import Linear.SchemeModuleOriginalCutActualSectionSequence
public import Linear.SchemeModuleActualCohomologyGroup
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf projectivePulledLinearKoszulForms
  projectivePulledLinearKoszulComplex
variable {n r : ℕ}
/-- EXACT original native endpoint sequence at t=r*q-r-1:
Gamma(O_V(t))->Gamma(O_S(t))->actual H^r(O_V(-r-1))->0.
Both maps are the actual original augmentation/Ext-class maps under
PROVED endpoint identifications. Agreement with an independently named
geometric quotient map and proper-duality transpose are separate tasks.
This is a statement definition,not a proof. -/
def projectivePulledOriginalCutActualSectionSequenceStatement
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
    (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      QuasiIso (originalChainCokernelTargetAugmentation
        (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
        (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) e)) : Prop :=
  let t : ℤ := (r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1
  let J := projectivePulledLinearSectionIdeal f V L w
  let hJ := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := homogeneousQuotientGrading J hJ
  letI := schemeModuleActualCohomologyAddCommGroup
    (Proj (homogeneousQuotientPiece V.ideal.toIdeal))
    (nativeProjectiveModuleSheaf (homogeneousQuotientPiece V.ideal.toIdeal)
      (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal))
      (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece V.ideal.toIdeal)) (-(r : ℤ)-1)) r
  let cut := nativeProjectiveModuleSheaf (homogeneousQuotientPiece J)
    (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece J))
    (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece J)) t
  let C := projectivePulledLinearKoszulComplex f V L hL w t
  let alpha := originalChainCokernelTargetAugmentation C
    (projectivePulledWholeCutResolutionTarget f V L hL w t) e
  let delta := schemeModuleOriginalCutActualSectionBoundary
    (projectivePulledLinearSectionClosedEmbedding f V L hL w) cut C r alpha he
    (projectivePulledOriginalKoszul_isZero_above f V L hL w t (r+1) (by omega))
    (projectivePulledOriginalKoszulTopOriginalCoefficientIso f V L hL w)
  let rho := schemeModuleOriginalCutActualSectionMap
    (projectivePulledLinearSectionClosedEmbedding f V L hL w) cut C alpha
    (projectivePulledOriginalKoszulZeroTwistIso f V L hL w t)
  Function.Surjective delta ∧
    ∀ s : Γ(cut,⊤),delta s = 0 ↔
      ∃ z : Γ(nativeProjectiveModuleSheaf (homogeneousQuotientPiece V.ideal.toIdeal)
        (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal))
        (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece V.ideal.toIdeal)) t,⊤),rho z = s
/-- Actual fixed-top roof exactness gives the stated original native
cut-section sequence;all endpoint comparison maps are constructed. -/
theorem projectivePulledOriginalCutActualSectionSequenceStatement_of_fixedTop
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
    (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      QuasiIso (originalChainCokernelTargetAugmentation
        (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
        (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) e))
    (h : projectivePulledOriginalFixedTopActualSectionStatement f V L hL w e he) :
    projectivePulledOriginalCutActualSectionSequenceStatement f V L hL w e he := by
  let t : ℤ := (r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1
  let J := projectivePulledLinearSectionIdeal f V L w
  let hJ := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := homogeneousQuotientGrading J hJ
  letI := schemeModuleActualCohomologyAddCommGroup
    (Proj (homogeneousQuotientPiece V.ideal.toIdeal))
    (nativeProjectiveModuleSheaf (homogeneousQuotientPiece V.ideal.toIdeal)
      (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal))
      (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece V.ideal.toIdeal)) (-(r : ℤ)-1)) r
  exact schemeModuleOriginalCutActualSection_exact
    (projectivePulledLinearSectionClosedEmbedding f V L hL w)
    (nativeProjectiveModuleSheaf (homogeneousQuotientPiece J)
      (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece J))
      (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece J)) t)
    (projectivePulledLinearKoszulComplex f V L hL w t) r
    (originalChainCokernelTargetAugmentation
      (projectivePulledLinearKoszulComplex f V L hL w t)
      (projectivePulledWholeCutResolutionTarget f V L hL w t) e) he
    (projectivePulledOriginalKoszul_isZero_above f V L hL w t (r+1) (by omega))
    (projectivePulledOriginalKoszulTopOriginalCoefficientIso f V L hL w)
    (projectivePulledOriginalKoszulZeroTwistIso f V L hL w t) h
/-- ONE m above the fixed lower bound precedes ALL original iterate
maps and parameters. No original-V Serre premise is left. Actual
augmentation e/he remains explicit until derived from original Setup. -/
theorem projectivePulledOriginal_uniformCutActualSectionSequence_above
    (V : IntegralProjectiveEquations n) (lower : ℕ) (hr : 0 < r) :
    ∃ m : ℕ,0 < m ∧ lower ≤ m ∧ ∀ D : ℕ,1 ≤ D →
      ∀ f : HomogeneousEndomorphism n,m*D < f.degree →
      ∀ (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
        (w : Fin (r+1) → ℂ),
      let t : ℤ := (r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1
      ∀ (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
          cokernel ((projectivePulledLinearKoszulComplex f V L hL w t).d 1 0) ≅
            projectivePulledWholeCutResolutionTarget f V L hL w t)
        (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
          QuasiIso (originalChainCokernelTargetAugmentation
            (projectivePulledLinearKoszulComplex f V L hL w t)
            (projectivePulledWholeCutResolutionTarget f V L hL w t) e)),
        projectivePulledOriginalCutActualSectionSequenceStatement f V L hL w e he := by
  obtain ⟨m,hm,hl,hAll⟩ := projectivePulledOriginal_uniformFixedTopActualSectionExact_above V lower hr
  refine ⟨m,hm,hl,?_⟩
  intro D hD f hd L hL w
  dsimp only
  intro e he
  exact projectivePulledOriginalCutActualSectionSequenceStatement_of_fixedTop
    f V L hL w e he (hAll D hD f hd L hL w e he)
end LinearStudy
