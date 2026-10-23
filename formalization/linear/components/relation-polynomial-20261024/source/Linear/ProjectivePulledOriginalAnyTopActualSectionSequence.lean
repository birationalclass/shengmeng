module
public import Linear.OriginalProjectiveStructureTwistSerreInterface
public import Linear.ProjectivePulledOriginalKoszulEndpointTwistIso
public import Linear.SchemeModuleOriginalActualSectionSerre
public import Linear.SchemeModuleOriginalActualSectionBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra HasFiniteBiproducts.of_hasFiniteProducts
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf projectivePulledLinearKoszulForms
  projectivePulledLinearKoszulComplex projectivePulledWholeCutResolutionTarget
  projectivePulledKoszulTopResolutionTarget
variable {n r : ℕ}
/-- Actual section-to-native-H exactness with ANY PROVED top coefficient
isomorphism for the SAME ORIGINAL complex for the SAME original Koszul roof
at t=r*q-r-1. This statement has NO Serre or desired exactness premise. The
original augmentation and its quasi-isomorphism remain explicit data. -/
def projectivePulledOriginalAnyTopActualSectionStatement
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
  ∀ (M : (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules)
    (phi : (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)).X r ≅ M),
  schemeModuleOriginalActualSectionExactStatement
    (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) r
    (originalChainCokernelTargetAugmentation
      (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
      (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) e) he
    (projectivePulledOriginalKoszul_isZero_above f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1) (r+1) (by omega))
    phi
/-- A fixed genuine geometric Serre bound now proves actual section-to-native-H
exactness; arbitrary-source Ext vanishing is not required. -/
theorem projectivePulledOriginalAnyTopActualSectionStatement_of_bound
    (hr : 0 < r)
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
    (N : ℕ) (hd : N+r+1 ≤ f.degree)
    (hSerre : projectivePulledOriginalStructureTwistSerreBoundStatement V N) :
    projectivePulledOriginalAnyTopActualSectionStatement f V L hL w e he := by
  dsimp only [projectivePulledOriginalAnyTopActualSectionStatement]
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  intro M phi
  exact schemeModuleOriginalActualSectionExact_of_unitSerre
    (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) r hr
    (originalChainCokernelTargetAugmentation
      (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
      (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) e) he
    (projectivePulledOriginalKoszul_isZero_above f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1) (r+1) (by omega))
    phi
    (fun s => nativeProjectiveModuleSheaf (homogeneousQuotientPiece V.ideal.toIdeal)
      (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal))
      (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece V.ideal.toIdeal)) s) N f.degree
    (projectivePulledOriginalTermTwistIso f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) hd hSerre
/-- Derive ONE m above any fixed lower bound BEFORE ALL original degrees,
iterate maps and parameters. Actual original-V Serre existence is PROVED,
not assumed. This is ACTUAL SECTION exactness of the original roof for ANY PROVED top identification,not yet
proper duality,original4.1/4.2 or a final nonzero prescribed section. -/
theorem projectivePulledOriginal_uniformAnyTopActualSectionExact_above
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
        projectivePulledOriginalAnyTopActualSectionStatement f V L hL w e he := by
  obtain ⟨N,hN,hSerre⟩ := originalProjectiveStructureTwist_globalUnitExtSerreBoundStatement V
  refine ⟨max (N+r+1) lower,by omega,le_max_right _ _,?_⟩
  intro D hD f hd L hL w
  dsimp only
  intro e he
  apply projectivePulledOriginalAnyTopActualSectionStatement_of_bound hr f V L hL w e he N
  · have hm : N+r+1 ≤ (max (N+r+1) lower)*D :=
      (le_max_left _ _).trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (max (N+r+1) lower) hD)
    omega
  · exact hSerre
end LinearStudy
