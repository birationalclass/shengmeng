module
public import Linear.NativeCoextensionSpecifiedNonzeroFunctionalLift
public import Linear.SchemeModuleOriginalSectionRelationDescent
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
/-- A nonzero ORIGINAL SECTION-RELATION functional is represented by a
nonzero ACTUAL coefficient map and its SAME original pushed-forward Ext
class under the constructed model trace. No top-H functional is supplied:
it is constructed by the new ORIGINAL boundary-linear quotient descent.
Actual exactness remains explicit;the concrete original Serre application
is the next obligation. Canonical/local-E/normalized trace remain open. -/
theorem nativeCoextensionSpecifiedTrace_original_section_relation_representative
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤) (q : ℕ) (hcard : Fintype.card σ=q+2)
    {G : (Proj B).Modules} (CC : ChainComplex (Proj B).Modules ℕ)
    (alpha : CC ⟶ (ChainComplex.single₀ (Proj B).Modules).obj G) (hAlpha : QuasiIso alpha)
    (hAbove : CategoryTheory.Limits.IsZero (CC.X ((q+1)+1)))
    (phi : CC.X (q+1) ≅ nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ)))
    (hExact : schemeModuleOriginalActualSectionExactStatement CC (q+1) alpha hAlpha hAbove phi) :
    let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
    letI : Module K Γ(G,⊤) := schemeModuleSectionsSpecModule piB G
    ∀ lambda : Module.Dual K Γ(G,⊤),lambda ≠ 0 →
      (∀ z : Γ(CC.X 0,⊤),lambda ((alpha.f 0).app ⊤ z)=0) →
      ∃ a : nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ)) ⟶
          nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
            (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
            (-(Fintype.card σ:ℤ)),a ≠ 0 ∧ ∀ s : Γ(G,⊤),
        schemeModuleExtSectionTracePairing
          (nativeCoextensionSpecifiedTopGlobalExtTrace B c hc hgenC q hcard)
          (schemeModuleExtClassCoefficientPushforwardAddHom
            (schemeModuleOriginalChainTopExtClassSmall CC (q+1) alpha hAlpha phi.hom
              (hAbove.eq_of_src _ _)) a) s=lambda s := by
  dsimp only
  let piB := Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))
  let F := nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ))
  let W := nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
    (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ))
  let H : Type := schemeModuleActualCohomology (Proj B) F (q+1)
  letI : Module K Γ(G,⊤) := schemeModuleSectionsSpecModule piB G
  letI : Module K H := schemeModuleActualHSpecModule piB F (q+1)
  intro lambda hne hrel
  have hdesc : ∃ ell : Module.Dual K H,ell ≠ 0 ∧
      ∀ s : Γ(G,⊤),ell (schemeModuleOriginalActualSectionBoundary CC (q+1) alpha hAlpha hAbove phi s)=lambda s :=
    schemeModuleOriginalActualSectionRelation_nonzero_descent (K:=K) (X:=Proj B) piB
      (E:=G) (M:=F) CC (q+1) alpha hAlpha hAbove phi hExact lambda hne hrel
  obtain ⟨ell,hell,hvalue⟩ := hdesc
  have hellAdd : ell.toAddMonoidHom ≠ 0 := by
    intro hz
    apply hell
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : H →+ K => f x) hz
  have hscalar (r : K) (x : H) :
      ell (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
        (originalGlobalModuleScalar (piB.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r)) F)) (q+1) x)=r * ell x := by
    change ell (r • x)=r * ell x
    exact ell.map_smul r x
  have hrep : ∃ a : F ⟶ W,a ≠ 0 ∧ ∀ x : H,
      nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard
        (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map a) (q+1) x)=ell x :=
    nativeCoextensionSpecifiedTrace_exists_nonzero_functional_lift_of_originalScalar
      (K:=K) (S:=S) (M:=M) (σ:=σ) B D hR hS c hc hgenC q hcard ell.toAddMonoidHom hscalar hellAdd
  obtain ⟨a,hane,ha⟩ := hrep
  refine ⟨a,hane,?_⟩
  intro s
  exact ((nativeCoextensionSpecifiedTopGlobalExtTrace_originalBoundary (K:=K) (S:=S) (σ:=σ)
    B c hc hgenC q hcard (G:=G) (F:=F) CC alpha hAlpha hAbove phi a s).symm.trans
      (ha (schemeModuleOriginalActualSectionBoundary CC (q+1) alpha hAlpha hAbove phi s))).trans (hvalue s)
end LinearStudy
