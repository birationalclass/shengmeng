module
public import Linear.NativeCoextensionSpecifiedNonzeroFunctionalLift
public import Linear.NativeCoextensionSpecifiedGlobalExtTrace
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
/-- The SAME nonzero actual representative works BEFORE ALL original
chain/Koszul roofs with the fixed top coefficient. Its SAME pushed-forward
original Ext class gives the prescribed functional on the actual original
section boundary under the constructed MODEL trace. Original alpha and its
quasi-isomorphism remain explicit;no canonical/local-E perfection claimed. -/
theorem nativeCoextensionSpecifiedTrace_exists_nonzero_original_boundary_representative
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
          (-(Fintype.card σ:ℤ)),a ≠ 0 ∧
      ∀ (G : (Proj B).Modules) (CC : ChainComplex (Proj B).Modules ℕ)
        (alpha : CC ⟶ (ChainComplex.single₀ (Proj B).Modules).obj G) (hAlpha : QuasiIso alpha)
        (hAbove : CategoryTheory.Limits.IsZero (CC.X ((q+1)+1)))
        (phi : CC.X (q+1) ≅ nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ)))
        (s : Γ(G,⊤)),
      schemeModuleExtSectionTracePairing
        (nativeCoextensionSpecifiedTopGlobalExtTrace B c hc hgenC q hcard)
        (schemeModuleExtClassCoefficientPushforwardAddHom
          (schemeModuleOriginalChainTopExtClassSmall CC (q+1) alpha hAlpha phi.hom
            (hAbove.eq_of_src _ _)) a) s =
        ell (schemeModuleOriginalActualSectionBoundary CC (q+1) alpha hAlpha hAbove phi s) := by
  have hrep : ∃ a : nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ)) ⟶
        nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
          (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
          (-(Fintype.card σ:ℤ)),
      a ≠ 0 ∧ ∀ x,nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard
        (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map a)
          (q+1) x)=ell x :=
    nativeCoextensionSpecifiedTrace_exists_nonzero_functional_lift_of_originalScalar
      (K:=K) (S:=S) (M:=M) (σ:=σ) B D hR hS c hc hgenC q hcard ell hlinear hell
  obtain ⟨a,hane,ha⟩ := hrep
  refine ⟨a,hane,?_⟩
  intro G CC alpha hAlpha hAbove phi s
  exact (nativeCoextensionSpecifiedTopGlobalExtTrace_originalBoundary (K:=K) (S:=S) (σ:=σ) B c hc hgenC q hcard
    (G:=G) (F:=nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ)))
    CC alpha hAlpha hAbove phi a s).symm.trans
      (ha (schemeModuleOriginalActualSectionBoundary CC (q+1) alpha hAlpha hAbove phi s))
end LinearStudy
