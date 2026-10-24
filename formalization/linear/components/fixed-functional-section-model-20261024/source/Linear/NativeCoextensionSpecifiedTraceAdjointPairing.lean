module
public import Linear.NativeCoextensionSpecifiedEvaluationTrace
public import Linear.NativeSpecifiedNormalizationCoefficientPairing
public import Linear.OriginalGradedCoextensionAdjointZero
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
/-- The ORIGINAL evaluation pairing at twist -card(sigma) is the
CONSTRUCTED model trace after the ACTUAL coefficient map supplied by
mathlib's original adjunction. The coefficient map's degree-zero property,
the exact Hom precomposition identity and actual-H naturality are PROVED.
No trace/pairing compatibility or perfect-pairing certificate is input. -/
theorem nativeCoextensionSpecifiedTopEvaluationTrace_adjointPairing
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    (psi : integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D
      (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ))))
    (x : schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B D hS (-(Fintype.card σ:ℤ))) (q+1)) :
    let f := coextensionOriginalAdjoint (S:=S) psi.1
    let hf := coextensionOriginalAdjoint_degreeZero (MvPolynomial.homogeneousSubmodule σ K)
      B D hS (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ))) (sub_self _) psi
    nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard
      (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map
        (nativeProjectiveDegreeZeroSheafMap B D (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) hS
          (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
          f hf (-(Fintype.card σ:ℤ)))) (q+1) x) =
      (show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) D
        (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ)))) from
        (nativeFiniteNormalization_specifiedActualTopHomDualIso B D hR hS c hc hgenC q hcard
          (-(Fintype.card σ:ℤ))).hom x) psi := by
  dsimp only
  let f := coextensionOriginalAdjoint (S:=S) psi.1
  let hf := coextensionOriginalAdjoint_degreeZero (MvPolynomial.homogeneousSubmodule σ K)
    B D hS (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ))) (sub_self _) psi
  have hp : integerGradedHomPrecomposition (MvPolynomial.homogeneousSubmodule σ K) D (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
      (f.restrictScalars (MvPolynomial σ K)) hf
      (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ)))
      (nativeCoextensionSpecifiedTopEvaluationHom B) = psi := by
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    rw [integerGradedHomPrecomposition_apply]
    change coextensionOriginalEvaluationAtOne (R:=MvPolynomial σ K) (S:=S)
      (coextensionOriginalAdjoint (S:=S) psi.1 y) = psi.1 y
    exact coextensionOriginalEvaluationAtOne_adjoint psi.1 y
  have h := nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficientPairing
    B D (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) hR hS
    (coextensionNormalizationBaseGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
    (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
    f hf c hc hgenC q hcard (-(Fintype.card σ:ℤ)) x
      (nativeCoextensionSpecifiedTopEvaluationHom B)
  rw [nativeCoextensionSpecifiedTopEvaluationTrace_apply]
  simpa only [hp] using h
end LinearStudy
