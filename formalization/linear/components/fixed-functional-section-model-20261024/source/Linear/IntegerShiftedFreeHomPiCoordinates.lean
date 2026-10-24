module
public import Linear.IntegerShiftedFreeHomCoordinates
public import Mathlib.Logic.Equiv.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy

/-- The ACTUAL original Submodule.pi tuple is the product of its actual
submodules. Reuses mathlib's original subtypePiEquivPi,with linearity
proved;no coordinate comparison is assumed. -/
def submodulePiUnivLinearEquiv {R M J : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (p : J → Submodule R M) :
    Submodule.pi Set.univ p ≃ₗ[R] (∀ j, p j) :=
  { toEquiv :=
      (Equiv.subtypeEquivRight (fun x : J → M => by
        change (∀ j, j ∈ Set.univ → x j ∈ p j) ↔ ∀ j, x j ∈ p j
        simp)).trans Equiv.subtypePiEquivPi
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The original polynomial tuple is unchanged coordinate by coordinate. -/
theorem submodulePiUnivLinearEquiv_apply {R M J : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (p : J → Submodule R M)
    (x : Submodule.pi Set.univ p) (j : J) :
    (submodulePiUnivLinearEquiv p x j).1 = x.1 j := rfl

/-- The inverse comparison also preserves each actual coordinate. -/
theorem submodulePiUnivLinearEquiv_symm_apply {R M J : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (p : J → Submodule R M)
    (x : ∀ j, p j) (j : J) :
    ((submodulePiUnivLinearEquiv p).symm x).1 j = (x j).1 := rfl

variable {K S J : Type*} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The ACTUAL homogeneous coordinate submodule is the product of its
original INTEGER degree pieces,including every negative ZERO piece. -/
def integerShiftedFreeDualCoordinatePiEquiv (w : J → ℤ) (d : ℤ) :
    integerShiftedFreeDualCoordinatePiece 𝓑 w d ≃ₗ[K]
      (∀ j, nativeProjectiveRingIntegerPiece 𝓑 (w j+d)) :=
  submodulePiUnivLinearEquiv _

variable [Fintype J] [DecidableEq J]

/-- Original homogeneous free Hom at degree -N and weights a_j+N
is canonically the product of the ORIGINAL degree-a_j pieces.
The degree cancellation is proved,not an extra comparison hypothesis. -/
def integerShiftedFreeHomNaturalCoordinatesEquiv (N : ℕ) (a : J → ℕ) :
    integerGradedHomPiece 𝓑
      (integerShiftedFreePiece 𝓑 (fun j => (a j : ℤ)+(N:ℤ))) (-(N:ℤ)) ≃ₗ[K]
      (∀ j, 𝓑 (a j)) :=
  (integerShiftedFreeHomCoordinatesEquiv 𝓑 (fun j => (a j : ℤ)+(N:ℤ)) (-(N:ℤ))).trans
    ((integerShiftedFreeDualCoordinatePiEquiv 𝓑 (fun j => (a j : ℤ)+(N:ℤ)) (-(N:ℤ))).trans
      (LinearEquiv.piCongrRight (fun j => LinearEquiv.ofEq _ _ (by
        simp [nativeProjectiveRingIntegerPiece]))))

/-- The original Hom-to-degree-piece comparison is evaluation on the
actual basis vector;the polynomial is unchanged by degree cancellation. -/
theorem integerShiftedFreeHomNaturalCoordinatesEquiv_apply (N : ℕ) (a : J → ℕ)
    (φ : integerGradedHomPiece 𝓑
      (integerShiftedFreePiece 𝓑 (fun j => (a j : ℤ)+(N:ℤ))) (-(N:ℤ))) (j : J) :
    (integerShiftedFreeHomNaturalCoordinatesEquiv 𝓑 N a φ j).1 = φ.1 (Pi.single j (1:S)) := by
  change (integerShiftedFreeHomCoordinatesEquiv 𝓑
    (fun j => (a j : ℤ)+(N:ℤ)) (-(N:ℤ)) φ).1 j = _
  exact integerShiftedFreeHomCoordinatesEquiv_apply 𝓑 _ _ φ j

end LinearStudy
