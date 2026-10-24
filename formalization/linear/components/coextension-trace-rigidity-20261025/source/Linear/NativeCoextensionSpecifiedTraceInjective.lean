module
public import Linear.NativeCoextensionSpecifiedEvaluationTrace
public import Linear.CoextensionDegreeZeroRigidity
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
/-- The SAME actual model trace is injective for the ORIGINAL faithful
finite domain normalization over an algebraically closed field. Actual
Hom0 is proved scalar via its original coextension adjunction. No global
CM,S2,locally free canonical module or proper-trace comparison is assumed. -/
theorem nativeCoextensionSpecifiedTopEvaluationTrace_injective
    [IsAlgClosed K] [FaithfulSMul (MvPolynomial σ K) S]
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) :
    Function.Injective (nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard) := by
  let V : Type := integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K)
    (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
    (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ)))
  let H := schemeModuleActualCohomology (Proj B)
    (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
      (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
      (-(Fintype.card σ:ℤ))) (q+1)
  let I := nativeFiniteNormalization_specifiedActualTopHomDualIso B
    (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
    (coextensionNormalizationBaseGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
    (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
    c hc hgenC q hcard (-(Fintype.card σ:ℤ))
  let e : H ≃+ Module.Dual K V := actualAbelianIsoAddEquiv (K:=K) (H:=H) (V:=V) I
  let lam : V := nativeCoextensionSpecifiedTopEvaluationHom B
  intro x y hxy
  apply e.injective
  apply LinearMap.ext
  intro phi
  let phi0 : integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K)
      (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) 0 :=
    ⟨phi.1,by simpa only [sub_self] using phi.property⟩
  obtain ⟨a,ha⟩ := coextensionDegreeZeroHom_exists_scalar_evaluation (σ:=σ) B phi0
  have hphi : phi=a • lam := by
    apply Subtype.ext
    apply LinearMap.ext
    intro ell
    exact ha ell
  rw [hphi,map_smul,map_smul]
  change e x lam=e y lam at hxy
  exact congrArg (fun z : K => a • z) hxy
end LinearStudy
