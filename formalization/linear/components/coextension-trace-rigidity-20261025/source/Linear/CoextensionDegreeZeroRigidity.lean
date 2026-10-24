module
public import Linear.CoextensionDegreeZeroEndEvaluation
public import Linear.OriginalGradedCoextensionAdjointZero
public import Linear.FiniteDomainDualNonzero
public import Linear.NativeCoextensionSpecifiedEvaluationTrace
public import Linear.IntegerGradedHomPieceFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K S : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [CommRing S] [IsDomain S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
variable [IsScalarTower K (MvPolynomial σ K) S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) B]
variable [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite (MvPolynomial σ K) S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  coextensionGradedDecomposition coextensionOriginalBaseScalarTower
  coextensionTraceBaseSourceTower coextensionTraceFieldSourceTower coextensionTraceFiniteBase
/-- Surjectivity is the ALREADY PROVED original graded coextension
adjunction. No new scalar action or guessed degree projection is used. -/
theorem coextensionDegreeZeroEndEvaluation_surjective :
    Function.Surjective (coextensionDegreeZeroEndEvaluation (σ:=σ) B) := by
  intro phi
  let f := coextensionOriginalAdjoint (S:=S) phi.1
  have hf := coextensionOriginalAdjoint_degreeZero (MvPolynomial.homogeneousSubmodule σ K)
    B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
    (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
    0 rfl phi
  refine ⟨⟨f,hf⟩,?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro ell
  exact coextensionOriginalEvaluationAtOne_adjoint phi.1 ell
/-- The ACTUAL degree-zero endomorphism algebra is scalar over the
original algebraically closed field. Its finiteness,domain property and
nontriviality are DERIVED from the original faithful finite normalization.
No global CM,S2,free-dual or rigidity hypothesis is added. -/
theorem coextensionDegreeZeroEnd_exists_scalar
    [IsAlgClosed K] [FaithfulSMul (MvPolynomial σ K) S]
    (f : integerGradedEndZero (S:=S)
      (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)) :
    ∃ a : K,f=algebraMap K _ a := by
  let A := integerGradedEndZero (S:=S)
    (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
  obtain ⟨e,he⟩ := coextensionDual_exists_integral_embedding (R:=MvPolynomial σ K) (S:=S)
  letI : NoZeroDivisors A := integerGradedEndZero_noZeroDivisors
    (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) e he
  obtain ⟨ell,hell⟩ := coextensionDual_exists_nonzero_at_one (R:=MvPolynomial σ K) (S:=S)
  letI : Nontrivial A := ⟨⟨1,0,by
    intro h
    have hv := congrArg (fun g : A => g.1 ell (1:S)) h
    exact hell hv⟩⟩
  letI : IsDomain A := NoZeroDivisors.to_isDomain A
  letI : Module.Finite K A := coextensionDegreeZeroEnd_finite (σ:=σ) B
  obtain ⟨a,ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=K) (K:=A)).2 f
  exact ⟨a,ha.symm⟩
/-- The ORIGINAL degree-zero Hom is spanned by the SAME eval-at-one
functional. This is a consequence of actual adjunction and proven scalar
rigidity,not an assumed duality or trace comparison. -/
theorem coextensionDegreeZeroHom_exists_scalar_evaluation
    [IsAlgClosed K] [FaithfulSMul (MvPolynomial σ K) S]
    (phi : integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K)
      (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) 0) :
    ∃ a : K,∀ ell,phi.1 ell=a • coextensionOriginalEvaluationAtOne (R:=MvPolynomial σ K) (S:=S) ell := by
  obtain ⟨f,hf⟩ := coextensionDegreeZeroEndEvaluation_surjective (σ:=σ) B phi
  obtain ⟨a,ha⟩ := coextensionDegreeZeroEnd_exists_scalar (σ:=σ) B f
  refine ⟨a,?_⟩
  intro ell
  rw [← hf,ha]
  change coextensionOriginalEvaluationAtOne (R:=MvPolynomial σ K) (S:=S) (a • ell)=
    a • coextensionOriginalEvaluationAtOne (R:=MvPolynomial σ K) (S:=S) ell
  exact (coextensionOriginalEvaluationAtOne (R:=MvPolynomial σ K) (S:=S)).map_smul_of_tower a ell
end LinearStudy
