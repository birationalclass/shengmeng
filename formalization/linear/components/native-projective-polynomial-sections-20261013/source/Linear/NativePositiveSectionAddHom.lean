module
public import Linear.NativeHomogeneousSectionFrame
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The original degree-m polynomial-to-section map is additive in the
actual module sheaf, so its finite monomial assembly uses actual sums. -/
def nativePositiveHomogeneousGlobalSectionAddHom (m : ℕ) :
    𝓑 m →+ Γ(nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (m : ℤ), ⊤) where
  toFun := nativePositiveHomogeneousGlobalSection 𝓑 m
  map_zero' := by
    apply Subtype.ext
    funext p
    exact LocalizedModule.zero_mk _
  map_add' := nativePositiveHomogeneousGlobalSection_add 𝓑 m
end LinearStudy
