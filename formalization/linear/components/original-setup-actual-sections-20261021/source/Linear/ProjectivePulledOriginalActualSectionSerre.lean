module
public import Linear.ProjectivePulledOriginalUnitCovariantSerre
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
/-- Actual section-to-native-H exactness for the SAME original Koszul roof
at t=r*q-r-1. This statement has NO Serre or desired exactness premise. The
original augmentation and its quasi-isomorphism remain explicit data. -/
def projectivePulledOriginalActualSectionAtSerreTwistStatement
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
  schemeModuleOriginalActualSectionExactStatement
    (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) r
    (originalChainCokernelTargetAugmentation
      (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
      (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) e) he
    (projectivePulledOriginalKoszul_isZero_above f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1) (r+1) (by omega))
    (projectivePulledOriginalKoszulTopTwistIso f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
/-- A fixed genuine geometric Serre bound now proves actual section-to-native-H
exactness; arbitrary-source Ext vanishing is not required. -/
theorem projectivePulledOriginalActualSectionAtSerreTwistStatement_of_bound
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
    projectivePulledOriginalActualSectionAtSerreTwistStatement f V L hL w e he := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  apply schemeModuleOriginalActualSectionExactStatement_of_unit
  exact projectivePulledOriginalUnitCovariantAtSerreTwistStatement_of_bound
    hr f V L hL w e he N hd hSerre
/-- Derive ONE m above any fixed lower bound BEFORE ALL original degrees,
iterate maps and parameters. Actual original-V Serre existence is PROVED,
not assumed. This is ACTUAL SECTION exactness of the original roof,not yet
proper duality,original4.1/4.2 or a final nonzero prescribed section. -/
theorem projectivePulledOriginal_uniformActualSectionExact_above
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
        projectivePulledOriginalActualSectionAtSerreTwistStatement f V L hL w e he := by
  obtain ⟨N,hN,hSerre⟩ := originalProjectiveStructureTwist_globalUnitExtSerreBoundStatement V
  refine ⟨max (N+r+1) lower,by omega,le_max_right _ _,?_⟩
  intro D hD f hd L hL w
  dsimp only
  intro e he
  apply projectivePulledOriginalActualSectionAtSerreTwistStatement_of_bound hr f V L hL w e he N
  · have hm : N+r+1 ≤ (max (N+r+1) lower)*D :=
      (le_max_left _ _).trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (max (N+r+1) lower) hD)
    omega
  · exact hSerre
end LinearStudy
