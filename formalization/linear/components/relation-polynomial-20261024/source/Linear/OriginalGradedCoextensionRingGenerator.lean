module
public import Linear.OriginalGradedCoextensionAdjointZero
public import Linear.NativeRingIntegerBaseGrade
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
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
/-- For the ORIGINAL ring coefficient,the adjoint map is multiplication
by its value at ONE. No sheaf Hom/section comparison is assumed. -/
theorem coextensionOriginalAdjoint_ring_generator (psi : Module.Dual R S) (x : S) :
    coextensionOriginalAdjoint (S:=S) psi x = x • coextensionOriginalAdjoint (S:=S) psi (1:S) := by
  simpa only [smul_eq_mul,mul_one] using (coextensionOriginalAdjoint (S:=S) psi).map_smul x (1:S)
/-- A NONZERO ORIGINAL R-functional gives a NONZERO actual element in
the SAME coextension by evaluating its adjoint at ONE. -/
theorem coextensionOriginalAdjoint_ring_one_ne_zero
    (psi : Module.Dual R S) (hne : psi ≠ 0) :
    coextensionOriginalAdjoint (S:=S) psi (1:S) ≠ 0 := by
  intro hz
  apply hne
  apply LinearMap.ext
  intro x
  change psi x=0
  have h := congrArg
    (fun z : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) => z x) hz
  change psi (x * (1:S))=0 at h
  simpa only [mul_one] using h
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
/-- A degree-zero ORIGINAL ring functional yields a degree-zero element
of the SAME coextension. This is the graded input for a fixed embedding
into S(m);canonical sheaves and cut support are not identified here. -/
theorem coextensionOriginalAdjoint_ring_one_mem_zero (d : ℤ) (hd : d=0)
    (psi : integerGradedHomPiece A (nativeProjectiveRingIntegerPiece B) d) :
    coextensionOriginalAdjoint (S:=S) psi.1 (1:S) ∈ coextensionGradedPiece A B 0 := by
  have hone : (1:S) ∈ nativeProjectiveRingIntegerPiece B 0 := by
    simpa [nativeProjectiveRingIntegerPiece] using (SetLike.one_mem_graded B)
  exact coextensionOriginalAdjoint_degreeZero A B (nativeProjectiveRingIntegerPiece B)
    (nativeProjectiveRingIntegerPiece_graded B) d hd psi 0 1 hone
end LinearStudy
