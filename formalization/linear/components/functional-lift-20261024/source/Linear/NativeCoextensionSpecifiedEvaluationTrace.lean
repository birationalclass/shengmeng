module
public import Linear.CoextensionNativeTopDualityInputs
public import Linear.NativeSpecifiedNormalizationTopPairing
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
theorem coextensionTraceBaseSourceTower : IsScalarTower (MvPolynomial σ K) S ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))) :=
  IsScalarTower.of_compHom (MvPolynomial σ K) S ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K)))
attribute [local instance] coextensionTraceBaseSourceTower
theorem coextensionTraceFieldSourceTower : IsScalarTower K S ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))) :=
  IsScalarTower.of_compHom K S ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K)))
attribute [local instance] coextensionTraceFieldSourceTower
theorem coextensionTraceFiniteBase : Module.Finite (MvPolynomial σ K) ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))) :=
  restrictedCoextensionDual_finite (R:=(MvPolynomial σ K)) (S:=S)
attribute [local instance] coextensionTraceFiniteBase
theorem coextensionTraceFiniteSource : Module.Finite S ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))) :=
  nativeCoextensionDual_finite_upper (R:=(MvPolynomial σ K)) (S:=S)
attribute [local instance] coextensionTraceFiniteSource
theorem coextensionTraceTorsionFree : Module.IsTorsionFree S ((ModuleCat.coextendScalars (algebraMap (MvPolynomial σ K) S)).obj (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K))) :=
  coextensionOriginalTopDualityTorsionFree (R:=(MvPolynomial σ K)) (S:=S)
attribute [local instance] coextensionTraceTorsionFree
attribute [local instance] schemeModuleActualCohomologyAddCommGroup
attribute [local irreducible] nativeFiniteNormalization_specifiedActualTopHomDualIso
/-- The ORIGINAL eval-at-one functional in the EXACT homogeneous Hom
piece selected by the SAME specified top duality at twist -card(sigma).
Its degree-zero membership is proved,not an input. -/
def nativeCoextensionSpecifiedTopEvaluationHom :
    integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ))) :=
  ⟨coextensionOriginalEvaluationAtOne (R:=(MvPolynomial σ K)) (S:=S),by
    simpa only [sub_self] using
      coextensionOriginalEvaluationAtOne_mem_integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) B⟩
/-- The SAME coextension's actual top-H trace candidate: evaluate its
SPECIFIED old comparison on the ORIGINAL functional ell↦ell(1).
All coextension finiteness,torsion freeness and graded actions are derived.
This is not an identification with a normalized geometric trace. -/
def nativeCoextensionSpecifiedTopEvaluationTrace
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) :
    schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
        (-(Fintype.card σ:ℤ))) (q+1) →+ K :=
  (Module.Dual.eval K _ (nativeCoextensionSpecifiedTopEvaluationHom B)).toAddMonoidHom.comp
    (nativeFiniteNormalization_specifiedActualTopHomDualIso B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
      (coextensionNormalizationBaseGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
      (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) c hc hgenC q hcard
        (-(Fintype.card σ:ℤ))).hom.hom
/-- Exact value on ORIGINAL actual H;the comparison is the SAME previously
specified map,not a chosen new duality or transported scalar action. -/
theorem nativeCoextensionSpecifiedTopEvaluationTrace_apply
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    (x : schemeModuleActualCohomology (Proj B)
      (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
        (-(Fintype.card σ:ℤ))) (q+1)) :
    nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard x =
    (show Module.Dual K (integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K) (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
        (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ)))) from
      (nativeFiniteNormalization_specifiedActualTopHomDualIso B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
        (coextensionNormalizationBaseGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
        (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) c hc hgenC q hcard
        (-(Fintype.card σ:ℤ))).hom x)
      (nativeCoextensionSpecifiedTopEvaluationHom B) := by
  rfl
end LinearStudy
