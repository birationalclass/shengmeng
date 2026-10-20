module
public import Linear.NativeKoszulCovariantSerreBound
public import Linear.SchemeModuleOriginalCovariantSerreStatement
public import Linear.ProjectivePulledOriginalTermTwistIso
public import Linear.ExtCovariantComplexSerreBound
public import Linear.ProjectivePulledOriginalCovariantExact
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
/-- UNPROVED geometric Serre premise on SAME original V,at ONE bound N.
A Prop STATEMENT only,not a proof or an assumed primitive. It concerns GLOBAL Ext
FROM the structure sheaf and is independent of f,L,w and iterate degree. -/
def projectivePulledOriginalStructureTwistSerreBoundStatement
    (V : IntegralProjectiveEquations n) (N : ℕ) : Prop :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  ∀ s : ℤ,(N : ℤ) ≤ s → ∀ i : ℕ,0 < i → Subsingleton
    (Ext.{0} (SheafOfModules.unit (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).ringCatSheaf)
      (nativeProjectiveModuleSheaf (homogeneousQuotientPiece V.ideal.toIdeal)
        (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal))
        (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece V.ideal.toIdeal)) s) i)
/-- Statement only:for EVERY O,a SINGLE twist Serre bound at N implies
actual exactness of SAME original C at t=r*q-r-1,q=f.degree. Same e/he,
actual top iso and all term isos retained. Geometric Serre is unproved. -/
def projectivePulledOriginalCovariantAtSerreTwistStatement
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)).d 1 0) ≅ (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)))
    (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      QuasiIso (originalChainCokernelTargetAugmentation (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) e))
    (N : ℕ) : Prop :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  schemeModuleOriginalCovariantSerreStatement
    (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) r
    (originalChainCokernelTargetAugmentation (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) e) he
    (projectivePulledOriginalKoszul_isZero_above f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1) (r+1) (by omega))
    (projectivePulledOriginalKoszulTopTwistIso f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
    (fun s => nativeProjectiveModuleSheaf (homogeneousQuotientPiece V.ideal.toIdeal)
      (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal))
      (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece V.ideal.toIdeal)) s) N f.degree
    (projectivePulledOriginalTermTwistIso f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))

/-- Prove the conditional SINGLE-bound implication at q>=N+r+1.
All sources O and their Serre premise stay inside the proved abstract
interface;no concrete unit-Ext comparison is replayed in the kernel. -/
theorem projectivePulledOriginalCovariantAtSerreTwistStatement_of_Serre
    (hr : 0 < r)
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)).d 1 0) ≅ (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)))
    (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      QuasiIso (originalChainCokernelTargetAugmentation (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) e))
    (N : ℕ) (hd : N+r+1 ≤ f.degree) :
    projectivePulledOriginalCovariantAtSerreTwistStatement f V L hL w e he N := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact schemeModuleOriginalCovariantSerreStatement_proof
    (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) r hr
    (originalChainCokernelTargetAugmentation (projectivePulledLinearKoszulComplex f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) (projectivePulledWholeCutResolutionTarget f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) e) he
    (projectivePulledOriginalKoszul_isZero_above f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1) (r+1) (by omega))
    (projectivePulledOriginalKoszulTopTwistIso f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1))
    (fun s => nativeProjectiveModuleSheaf (homogeneousQuotientPiece V.ideal.toIdeal)
      (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal))
      (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece V.ideal.toIdeal)) s) N f.degree
    (projectivePulledOriginalTermTwistIso f V L hL w ((r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1)) hd

/-- m=N+r+1 is fixed BEFORE all original degrees D,all iterate maps f,
all parameters L,w and all sources O satisfying the SINGLE bound at N.
This proves the conditional implication,NOT the existence of Serre N
or completion of original Lemma4.2. -/
theorem projectivePulledOriginal_uniformCovariantExact_from_Serre
    (V : IntegralProjectiveEquations n) (N : ℕ) (hr : 0 < r) :
    ∃ m : ℕ,0 < m ∧ ∀ D : ℕ,1 ≤ D → ∀ f : HomogeneousEndomorphism n,m*D < f.degree →
      ∀ (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
        (w : Fin (r+1) → ℂ),
      let k : ℤ := (r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1
      ∀ (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
          cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
            projectivePulledWholeCutResolutionTarget f V L hL w k)
        (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
          QuasiIso (originalChainCokernelTargetAugmentation
            (projectivePulledLinearKoszulComplex f V L hL w k)
            (projectivePulledWholeCutResolutionTarget f V L hL w k) e)),
        projectivePulledOriginalCovariantAtSerreTwistStatement f V L hL w e he N := by
  refine ⟨N+r+1,by omega,?_⟩
  intro D hD f hd L hL w
  dsimp only
  intro e he
  apply projectivePulledOriginalCovariantAtSerreTwistStatement_of_Serre hr f V L hL w e he N
  have hm : N+r+1 ≤ (N+r+1)*D := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N+r+1) hD
  omega
/-- The SAME uniform cohomological degree can be chosen ABOVE any
previously fixed embedding/polynomial-extension bound. This permits
reuse of the PUBLIC fixed-degree extension infrastructure without
claiming a new nonzero section or the original final polynomial. -/
theorem projectivePulledOriginal_uniformCovariantExact_above_from_Serre
    (V : IntegralProjectiveEquations n) (N lower : ℕ) (hr : 0 < r) :
    ∃ m : ℕ,0 < m ∧ lower ≤ m ∧ ∀ D : ℕ,1 ≤ D → ∀ f : HomogeneousEndomorphism n,m*D < f.degree →
      ∀ (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
        (w : Fin (r+1) → ℂ),
      let k : ℤ := (r : ℤ)*(f.degree : ℤ)-(r : ℤ)-1
      ∀ (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
          cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
            projectivePulledWholeCutResolutionTarget f V L hL w k)
        (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
          QuasiIso (originalChainCokernelTargetAugmentation
            (projectivePulledLinearKoszulComplex f V L hL w k)
            (projectivePulledWholeCutResolutionTarget f V L hL w k) e)),
        projectivePulledOriginalCovariantAtSerreTwistStatement f V L hL w e he N := by
  obtain ⟨m,hm,hExact⟩ := projectivePulledOriginal_uniformCovariantExact_from_Serre V N hr
  refine ⟨max m lower,lt_of_lt_of_le hm (le_max_left _ _),le_max_right _ _,?_⟩
  intro D hD f hd
  exact hExact D hD f
    (lt_of_le_of_lt (Nat.mul_le_mul_right D (le_max_left m lower)) hd)
end LinearStudy
