module
public import Linear.NativeProjectiveLaurentFactors
public import Linear.NativeProjectiveHomogeneousSMul
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {K : Type u} [Field K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual sheaf multiplication, inherited from multiplication in the original
polynomial ring. No Laurent comparison is used in its construction. -/
def coordinateNativePolynomialMultiplication (m : ℕ)
    (p : homogeneousSubmodule σ K m) (k : ℤ) :
    coordinateNativeIntegerTwist (K := K) (σ := σ) k ⟶
      coordinateNativeIntegerTwist (K := K) (σ := σ) (k+(m:ℤ)) :=
  LinearStudy.nativeProjectiveHomogeneousSMul (homogeneousSubmodule σ K)
    (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
    (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K))
    p.1 m p.property k

/-- On every open, the actual map multiplies each prime-localized value
by the original homogeneous polynomial. -/
theorem coordinateNativePolynomialMultiplication_value (m : ℕ)
    (p : homogeneousSubmodule σ K m) (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top (homogeneousSubmodule σ K)))ᵒᵖ)
    (s : LinearStudy.nativeProjectiveModuleSections (homogeneousSubmodule σ K)
      (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
      (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K)) k U)
    (x : U.unop) :
    (((coordinateNativePolynomialMultiplication m p k).val.app U) s).1 x =
      p.1 • s.1 x := by
  exact LinearStudy.nativeProjectiveHomogeneousSMul_section_value
    (homogeneousSubmodule σ K)
    (LinearStudy.nativeProjectiveRingIntegerPiece (homogeneousSubmodule σ K))
    (LinearStudy.nativeProjectiveRingIntegerPiece_graded (homogeneousSubmodule σ K))
    p.1 m p.property k U s x
end MvPolynomial
