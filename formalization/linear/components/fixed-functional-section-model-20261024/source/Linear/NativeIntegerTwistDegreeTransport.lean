module
public import Linear.NativeProjectiveRingIntegerPieces
public import Mathlib.CategoryTheory.EqToHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Genuine equality transport between the original ring integer-twist
sheaves on the same original Proj. -/
def nativeRingIntegerTwistDegreeCast {d d' : ℤ} (h : d=d') :
    nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) d ⟶
    nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) d' :=
  eqToHom (congrArg (fun k : ℤ => nativeProjectiveModuleSheaf 𝓑
    (nativeProjectiveRingIntegerPiece 𝓑) (nativeProjectiveRingIntegerPiece_graded 𝓑) k) h)

/-- The original degree equality transport preserves the actual value
at every original prime on every original open. -/
theorem nativeRingIntegerTwistDegreeCast_value {d d' : ℤ} (h : d=d')
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (s : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) d U) (p : U.unop) :
    (((nativeRingIntegerTwistDegreeCast 𝓑 h).val.app U) s).1 p = s.1 p := by
  cases h
  rfl

end LinearStudy
