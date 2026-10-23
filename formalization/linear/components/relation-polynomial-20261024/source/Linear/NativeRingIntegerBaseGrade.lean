module
public import Linear.NativeProjectiveRingIntegerPieces
public import Linear.NormalizationHomogeneousChartMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
/-- The actual integer grading of the source ring respects the original
base-ring action. No overlap-map implementation or dual module is needed. -/
theorem nativeRingIntegerBaseGradeCompatibility :
    ∀ d : ℕ,∀ j : ℤ,∀ z : R,z ∈ A d →
      ∀ x : S,x ∈ nativeProjectiveRingIntegerPiece B j →
        z • x ∈ nativeProjectiveRingIntegerPiece B ((d : ℤ)+j) := by
  intro d j z hz x hx
  rw [Algebra.smul_def]
  exact nativeProjectiveRingIntegerPiece_graded B d j (algebraMap R S z)
    ((normalizationBaseGradedRingHom A B).map_mem hz) x hx
end LinearStudy
