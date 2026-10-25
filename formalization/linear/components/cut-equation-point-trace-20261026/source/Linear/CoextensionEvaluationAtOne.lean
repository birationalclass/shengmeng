module
public import Linear.CoextensionBaseGradeCompatibility
public import Linear.ActualPresentationGradedDualKernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul A B]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
/-- The ORIGINAL R-linear evaluation at 1 on the SAME native coextension
module,with its ORIGINAL R action. No geometric trace is identified. -/
def coextensionOriginalEvaluationAtOne :
    Module.Dual R ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) :=
  (Module.Dual.eval R S (1:S)).comp
    (coextensionOriginalDualEquiv (R:=R) (S:=S)).toLinearMap
/-- The constructed linear functional has EXACT original value ell(1). -/
theorem coextensionOriginalEvaluationAtOne_apply
    (ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)) :
    coextensionOriginalEvaluationAtOne (R:=R) (S:=S) ell = ell (1:S) := by
  rfl
/-- Actual eval-at-one is homogeneous of degree ZERO for the SAME
constructed coextension integer grading,including all negative degrees.
This is an ORIGINAL homogeneous-Hom membership,not a canonical sheaf input. -/
theorem coextensionOriginalEvaluationAtOne_mem_integerGradedHomPiece :
    coextensionOriginalEvaluationAtOne (R:=R) (S:=S) ∈
      integerGradedHomPiece A (coextensionGradedPiece A B) 0 := by
  intro j ell hell
  have h := (coextensionGradedPiece_mem_iff A B j ell).mp hell 0 (1:S)
    (SetLike.one_mem_graded B)
  have hh : ell (1:S) = gradedIntegerProjection A j (ell (1:S)) := by
    simpa only [Int.natCast_zero,zero_add] using h
  simpa only [add_zero,coextensionOriginalEvaluationAtOne_apply] using
    nativeProjectiveRingIntegerPiece_mem_of_projection A j (ell (1:S)) hh
end LinearStudy
