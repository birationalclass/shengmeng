module
public import Linear.SchemeModuleOriginalSectionRelationRepresentative
public import Linear.NativeCoextensionFixedPolynomialRepresentative
public import Linear.NativeCoextensionFixedPolynomialFunctional
public import Linear.SchemeModuleOriginalSectionRelationDescent
public import Linear.NativeCoextensionOriginalRingRepresentative
public import Linear.NativeCoextensionSpecifiedGradedRepresentative
public import Linear.NativeCoextensionSpecifiedTraceAdjointPairing
public import Linear.IntegerGradedHomPieceFinite
public import Linear.FiniteAdditiveDualNonzeroRepresentative
public import Linear.OriginalGradedCoextensionRingGenerator
public import Linear.NativeRingIntegerDecomposition
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
attribute [local instance] nativeProjectiveRingIntegerDecomposition
attribute [local irreducible] nativeProjectiveModuleSheaf
attribute [local irreducible] nativeCoextensionFixedPolynomialFunctionalStatement
attribute [local irreducible] schemeModuleOriginalSectionRelationRepresentativeStatement
  nativeCoextensionFixedPolynomialRepresentativeStatement
/-- Complete original relation-to-polynomial proposition,using the
EXPOSED generic original-boundary statement with the FULL per-functional
same-representative polynomial predicate. STATEMENT only. Both definitions
are printed in the exact audit;no construction is erased or assumed. -/
def nativeCoextensionOriginalRelationPolynomialStatement
    {τ : Type} (P : MvPolynomial τ K →ₐ[K] S) (I : Ideal (MvPolynomial τ K))
    (m : ℕ)
    (e : ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))) →ₗ[S] S)
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    {G : (Proj B).Modules} (CC : ChainComplex (Proj B).Modules ℕ)
    (alpha : CC ⟶ (ChainComplex.single₀ (Proj B).Modules).obj G) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (CC.X ((q+1)+1)))
    (phi : CC.X (q+1) ≅ nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
      (nativeProjectiveRingIntegerPiece_graded B) (-(Fintype.card σ:ℤ))) : Prop :=
  let D := nativeProjectiveRingIntegerPiece B
  let hS := nativeProjectiveRingIntegerPiece_graded B
  let F := nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ))
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let Rep := fun ell : schemeModuleActualCohomology (Proj B) F (q+1) →+ K =>
    nativeCoextensionFixedPolynomialRepresentativeStatement B P I m e c hc hgenC q hcard ell
  schemeModuleOriginalSectionRelationRepresentativeStatement piB CC (q+1) alpha hAlpha hAbove phi Rep
/-- Compose the PROVED original boundary descent with the ACTUAL fixed
polynomial theorem. Exactness and fixed polynomial theorem are explicit
here;the uniform concrete original-V integration remains UNVERIFIED. -/
theorem nativeCoextensionOriginalRelationPolynomialStatement_of_exact
    {τ : Type} (P : MvPolynomial τ K →ₐ[K] S) (I : Ideal (MvPolynomial τ K))
    (m : ℕ)
    (e : ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))) →ₗ[S] S)
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    {G : (Proj B).Modules} (CC : ChainComplex (Proj B).Modules ℕ)
    (alpha : CC ⟶ (ChainComplex.single₀ (Proj B).Modules).obj G) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (CC.X ((q+1)+1)))
    (phi : CC.X (q+1) ≅ nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
      (nativeProjectiveRingIntegerPiece_graded B) (-(Fintype.card σ:ℤ)))
    (hExact : schemeModuleOriginalActualSectionExactStatement CC (q+1) alpha hAlpha hAbove phi)
    (hpoly : nativeCoextensionFixedPolynomialFunctionalStatement B P I m e c hc hgenC q hcard) :
    nativeCoextensionOriginalRelationPolynomialStatement B P I m e c hc hgenC q hcard CC alpha hAlpha hAbove phi := by
  dsimp only [nativeCoextensionOriginalRelationPolynomialStatement]
  let D := nativeProjectiveRingIntegerPiece B
  let hS := nativeProjectiveRingIntegerPiece_graded B
  let F := nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ))
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let Rep := fun ell : schemeModuleActualCohomology (Proj B) F (q+1) →+ K =>
    nativeCoextensionFixedPolynomialRepresentativeStatement B P I m e c hc hgenC q hcard ell
  exact schemeModuleOriginalSectionRelationRepresentativeStatement_of_exact
    (K:=K) (X:=Proj B) piB (E:=G) (M:=F) CC (q+1) alpha hAlpha hAbove phi Rep hExact
      (fun ell hlinear hell => nativeCoextensionFixedPolynomialRepresentativeStatement_of_functional
        (K:=K) (S:=S) (σ:=σ) (τ:=τ) B P I m e c hc hgenC q hcard ell hlinear hell hpoly)
end LinearStudy
