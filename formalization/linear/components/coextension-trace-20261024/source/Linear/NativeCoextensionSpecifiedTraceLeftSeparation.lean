module
public import Linear.NativeCoextensionSpecifiedTraceAdjointPairing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
/-- The CONSTRUCTED model trace separates ORIGINAL actual top-H classes
by actual sheaf coefficient maps into the SAME C(-card sigma).
Only a separating family coming from the proved graded adjunction is
needed;no global-Hom/graded-Hom isomorphism or nondegeneracy is input. -/
theorem nativeCoextensionSpecifiedTrace_actualHom_left_separates
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    (x : schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ))) (q+1))
    (hz : ∀ a : nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ)) ⟶
        nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
          (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
          (-(Fintype.card σ:ℤ)),
      nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard
        (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map a)
          (q+1) x)=0) : x=0 := by
  apply nativeFiniteNormalization_specifiedActualTopHomDualIso_left_nondegenerate
    B D hR hS c hc hgenC q hcard (-(Fintype.card σ:ℤ)) x
  intro psi
  have h := nativeCoextensionSpecifiedTopEvaluationTrace_adjointPairing
    B D hR hS c hc hgenC q hcard psi x
  dsimp only at h
  exact h.symm.trans (hz _)
end LinearStudy
