module
public import Linear.NativeCoextensionSpecifiedEvaluationTrace
public import Linear.FiniteDomainDualNonzero
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
/-- In a FAITHFUL finite domain normalization,the ORIGINAL degree-zero
functional ell↦ell(1) is nonzero,using the existing fraction-field proof. -/
theorem nativeCoextensionSpecifiedTopEvaluationHom_ne_zero
    [FaithfulSMul (MvPolynomial σ K) S] :
    nativeCoextensionSpecifiedTopEvaluationHom (σ:=σ) B ≠ 0 := by
  intro hz
  obtain ⟨ell,hell⟩ := coextensionDual_exists_nonzero_at_one
    (R:=MvPolynomial σ K) (S:=S)
  have h := congrArg (fun phi => phi.1 ell) hz
  exact hell h
/-- The model trace actually takes value ONE for a faithful normalization.
Neither nonzero trace nor a normalization certificate is an input. -/
theorem nativeCoextensionSpecifiedTopEvaluationTrace_exists_one
    [FaithfulSMul (MvPolynomial σ K) S]
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) :
    ∃ x,nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard x=1 := by
  let V : Type := integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
    (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ)))
  let lam : V := nativeCoextensionSpecifiedTopEvaluationHom B
  have hne : lam ≠ 0 := nativeCoextensionSpecifiedTopEvaluationHom_ne_zero (σ:=σ) B
  letI : Module.Free K V := by
    convert! (Module.Free.of_divisionRing K V) using 1
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one K (V:=V) hne
  let I := nativeFiniteNormalization_specifiedActualTopHomDualIso B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
    (coextensionNormalizationBaseGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
    (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) c hc hgenC q hcard
      (-(Fintype.card σ:ℤ))
  let H := schemeModuleActualCohomology (Proj B)
    (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
      (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
      (-(Fintype.card σ:ℤ))) (q+1)
  let e : H ≃+ Module.Dual K V := actualAbelianIsoAddEquiv (K:=K) (H:=H) (V:=V) I
  obtain ⟨x,hx⟩ := e.surjective f
  refine ⟨x,?_⟩
  change e x lam=1
  rw [hx]
  exact hf
end LinearStudy
