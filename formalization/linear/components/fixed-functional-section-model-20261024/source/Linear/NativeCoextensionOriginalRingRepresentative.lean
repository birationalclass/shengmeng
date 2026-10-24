module
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
/-- For the ORIGINAL ring coefficient,an actual nonzero top-H functional
constructs a NONZERO degree-zero element of SAME coextension C. Its
ORIGINAL graded R-functional witness is retained with exact comparison
values. This supplies the input to the fixed graded embedding;no local
support or canonical omega identification is asserted. -/
theorem nativeCoextensionSpecifiedTopDual_ring_exists_nonzero_zero_degree_element
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    (ell : schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
        (nativeProjectiveRingIntegerPiece_graded B) (-(Fintype.card σ:ℤ))) (q+1) →+ K)
    (hlinear : ∀ r : K,∀ x,
      ell (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
        (originalGlobalModuleScalar
          ((Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))).appTop
            ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r))
          (nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
            (nativeProjectiveRingIntegerPiece_graded B) (-(Fintype.card σ:ℤ))))) (q+1) x)=r * ell x)
    (hell : ell ≠ 0) :
    let A := MvPolynomial.homogeneousSubmodule σ K
    let D := nativeProjectiveRingIntegerPiece B
    let C := (ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))
    ∃ z : C,z ∈ coextensionGradedPiece A B 0 ∧ z ≠ 0 ∧
      ∃ psi : integerGradedHomPiece A D (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ))),
        z=coextensionOriginalAdjoint (S:=S) psi.1 (1:S) ∧ ∀ x,
          actualAbelianIsoAddEquiv
            (nativeFiniteNormalization_specifiedActualTopHomDualIso B D
              (nativeRingIntegerBaseGradeCompatibility A B) (nativeProjectiveRingIntegerPiece_graded B)
              c hc hgenC q hcard (-(Fintype.card σ:ℤ))) x psi=ell x := by
  dsimp only
  let A := MvPolynomial.homogeneousSubmodule σ K
  let D := nativeProjectiveRingIntegerPiece B
  let hR := nativeRingIntegerBaseGradeCompatibility A B
  let hS := nativeProjectiveRingIntegerPiece_graded B
  let H := schemeModuleActualCohomology (Proj B)
    (nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ))) (q+1)
  let V : Type := integerGradedHomPiece A D (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ)))
  have hrep : ∃ psi : V,psi ≠ 0 ∧ ∀ x : H,
      actualAbelianIsoAddEquiv
        (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS
          c hc hgenC q hcard (-(Fintype.card σ:ℤ))) x psi=ell x :=
    nativeCoextensionSpecifiedTopDual_exists_nonzero_graded_representative
      (K:=K) (S:=S) (M:=S) (σ:=σ) B D hR hS c hc hgenC q hcard ell hlinear hell
  obtain ⟨psi,hpsi,hvalue⟩ := hrep
  have hpsiVal : psi.1 ≠ 0 := by
    intro hz
    apply hpsi
    apply Subtype.ext
    exact hz
  refine ⟨coextensionOriginalAdjoint (S:=S) psi.1 (1:S),?_,?_,psi,rfl,hvalue⟩
  · exact coextensionOriginalAdjoint_ring_one_mem_zero A B _ (sub_self _) psi
  · exact coextensionOriginalAdjoint_ring_one_ne_zero psi.1 hpsiVal
end LinearStudy
