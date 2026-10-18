module
public import Linear.IntegerGradedKernelGenerators
public import Linear.NativeProjectiveModuleSheafMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {K S E F : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup E] [Module K E] [Module S E] [IsScalarTower K S E]
variable [AddCommGroup F] [Module K F] [Module S F]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (ℰ : ℤ → Submodule K E) (ℱ : ℤ → Submodule K F)
variable (b : E →ₗ[S] F)

/-- The actual kernel grading is the inverse image of the actual source
pieces under its original inclusion, not a supplied kernel model. -/
def nativeProjectiveKernelPiece (d : ℤ) : Submodule K b.ker :=
  integerGradedSubmodulePiece ℰ (b.ker.restrictScalars K) d

/-- Actual homogeneous scalar multiplication preserves the actual kernel
pieces. Kernel membership itself uses the original upper-ring linear map. -/
theorem nativeProjectiveKernelPiece_graded
    (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
      ∀ x : E, x ∈ ℰ d → c • x ∈ ℰ ((n : ℤ) + d))
    (n : ℕ) (d : ℤ) (c : S) (hc : c ∈ 𝓑 n) (x : b.ker)
    (hx : x ∈ nativeProjectiveKernelPiece ℰ b d) :
    c • x ∈ nativeProjectiveKernelPiece ℰ b ((n : ℤ) + d) :=
  hE n d c hc (x : E) hx

/-- The actual kernel of a degree-zero map has an internal integer
decomposition, derived from the original decompositions and map. -/
@[instance_reducible] def nativeProjectiveKernelDecomposition
    [DirectSum.Decomposition ℰ] [DirectSum.Decomposition ℱ]
    (hh : ∀ d : ℤ, ∀ x : E, x ∈ ℰ d → b x ∈ ℱ d) :
    DirectSum.Decomposition (nativeProjectiveKernelPiece ℰ b) :=
  integerGradedSubmoduleDecomposition ℰ (b.ker.restrictScalars K)
    (integerDegreeZeroMap_kernel_isHomogeneous ℰ ℱ b hh)

end LinearStudy
