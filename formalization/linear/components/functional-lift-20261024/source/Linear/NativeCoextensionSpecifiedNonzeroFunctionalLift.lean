module
public import Linear.NativeCoextensionSpecifiedFunctionalLift
public import Linear.SchemeModuleActualTraceRepresentingNonzero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K S : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [CommRing S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
variable [IsScalarTower K (MvPolynomial σ K) S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) B]
variable [IsDomain S] [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite (MvPolynomial σ K) S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  coextensionGradedDecomposition coextensionOriginalBaseScalarTower
attribute [local instance] coextensionTraceBaseSourceTower coextensionTraceFieldSourceTower
  coextensionTraceFiniteBase coextensionTraceFiniteSource coextensionTraceTorsionFree
  schemeModuleActualCohomologyAddCommGroup
attribute [local irreducible] nativeFiniteNormalization_specifiedActualTopHomDualIso
variable {M : Type} [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M] [Module S M]
variable [IsScalarTower (MvPolynomial σ K) S M] [IsScalarTower K (MvPolynomial σ K) M] [IsScalarTower K S M]
variable (D : ℤ → Submodule K M) [DirectSum.Decomposition D]
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ z : MvPolynomial σ K,z ∈ MvPolynomial.homogeneousSubmodule σ K n →
  ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ z : S,z ∈ B n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable [Module.IsTorsionFree S M] [Module.Finite (MvPolynomial σ K) M] [Module.Finite S M]
attribute [local irreducible] nativeCoextensionSpecifiedTopEvaluationTrace integerGradedHomPrecomposition
  nativeProjectiveModuleSheaf nativeProjectiveDegreeZeroSheafMap
include hR in
/-- A nonzero ORIGINAL scalar-linear functional has a nonzero ACTUAL
coefficient map representative under the constructed model trace. No
nonzero section of canonical omega or final polynomial is claimed. -/
theorem nativeCoextensionSpecifiedTrace_exists_nonzero_functional_lift_of_originalScalar
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    (ell : schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ))) (q+1) →+ K)
    (hlinear : ∀ r : K,∀ x,
      ell (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
        (originalGlobalModuleScalar
          ((Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))).appTop
            ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r))
          (nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ))))) (q+1) x)=r * ell x) (hell : ell ≠ 0) :
    ∃ a : nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ)) ⟶
        nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
          (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
          (-(Fintype.card σ:ℤ)),
      a ≠ 0 ∧ ∀ x,nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard
        (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map a)
          (q+1) x)=ell x := by
  have hrep : ∃ a : nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ)) ⟶
      nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
        (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
        (-(Fintype.card σ:ℤ)),
      ∀ x,nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard
        (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map a) (q+1) x)=ell x :=
    nativeCoextensionSpecifiedTrace_exists_functional_lift_of_originalScalar
      (K:=K) (S:=S) (M:=M) (σ:=σ) B D hR hS c hc hgenC q hcard ell hlinear
  obtain ⟨a,ha⟩ := hrep
  have hane : a ≠ 0 := schemeModuleActualTraceRepresentingMap_ne_zero (K:=K) (Proj B)
    (M:=nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ)))
    (W:=nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
      (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
      (-(Fintype.card σ:ℤ))) (q+1)
    (nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard) ell hell a ha
  exact ⟨a,hane,ha⟩
end LinearStudy
