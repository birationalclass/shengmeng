module
public import Linear.ProjectivePulledOriginalFixedTopActualSectionSequence
public import Linear.SchemeModuleOriginalSectionRelationDescent
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] schemeModuleActualCohomologyAddCommGroup
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf projectivePulledLinearKoszulForms
  projectivePulledLinearKoszulComplex projectivePulledWholeCutResolutionTarget
  projectivePulledKoszulTopResolutionTarget
variable {n r : ℕ}
/-- Exact ORIGINAL fixed-top section relation statement. This definition
only exposes the proposition for review;it proves nothing by itself. -/
def projectivePulledOriginalFixedTopNonzeroRelationStatement
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
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let t : ℤ := (r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  let CC := projectivePulledLinearKoszulComplex f V L hL w t
  let G := projectivePulledWholeCutResolutionTarget f V L hL w t
  let F := nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
    (nativeProjectiveRingIntegerPiece_graded B) (-(r : ℤ)-1)
  let pi := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (B 0)))
  let alpha := originalChainCokernelTargetAugmentation CC G e
  let hAbove := projectivePulledOriginalKoszul_isZero_above f V L hL w t (r+1) (by omega)
  let phi := projectivePulledOriginalKoszulTopOriginalCoefficientIso f V L hL w
  letI : Module ℂ Γ(G,⊤) := schemeModuleSectionsSpecModule pi G
  letI : Module ℂ (schemeModuleActualCohomology (Proj B) F r) := schemeModuleActualHSpecModule pi F r
  ∀ lambda : Module.Dual ℂ Γ(G,⊤),lambda ≠ 0 →
    (∀ z : Γ(CC.X 0,⊤),lambda ((alpha.f 0).app ⊤ z)=0) →
    ∃ ell : Module.Dual ℂ (schemeModuleActualCohomology (Proj B) F r),ell ≠ 0 ∧
      ∀ s : Γ(G,⊤),ell (schemeModuleOriginalActualSectionBoundary CC r alpha he hAbove phi s)=lambda s
/-- Transfer actual fixed-top exactness to the SAME actual boundary's
base-field-linear functional descent. Exactness is explicit only in
this intermediate lemma;the following theorem supplies it from Serre. -/
theorem projectivePulledOriginalFixedTopNonzeroRelationStatement_of_exact
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
    (hExact : projectivePulledOriginalFixedTopActualSectionStatement f V L hL w e he) :
    projectivePulledOriginalFixedTopNonzeroRelationStatement f V L hL w e he := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  dsimp only [projectivePulledOriginalFixedTopNonzeroRelationStatement]
  exact schemeModuleOriginalActualSectionRelation_nonzero_descent (K:=ℂ)
    (Proj.toSpecZero (homogeneousQuotientPiece V.ideal.toIdeal) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (homogeneousQuotientPiece V.ideal.toIdeal 0))))
    (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) r
    (originalChainCokernelTargetAugmentation
      (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
      (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) e) he
    (projectivePulledOriginalKoszul_isZero_above f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1) (r+1) (by omega))
    (projectivePulledOriginalKoszulTopOriginalCoefficientIso f V L hL w) hExact
/-- On ORIGINAL V,ONE bound m precedes ALL degrees,iterate maps,parameters,
augmentations and section relations. Actual original-V Serre DISCHARGES
exactness. No canonical identification,local support or final Q claimed. -/
theorem projectivePulledOriginal_uniform_nonzero_relation_descent_above
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
        projectivePulledOriginalFixedTopNonzeroRelationStatement f V L hL w e he := by
  obtain ⟨m,hm,hbound,hActual⟩ := projectivePulledOriginal_uniformFixedTopActualSectionExact_above V lower hr
  refine ⟨m,hm,hbound,?_⟩
  intro D hD f hd L hL w
  dsimp only
  intro e he
  exact projectivePulledOriginalFixedTopNonzeroRelationStatement_of_exact f V L hL w e he
    (hActual D hD f hd L hL w e he)
end LinearStudy
