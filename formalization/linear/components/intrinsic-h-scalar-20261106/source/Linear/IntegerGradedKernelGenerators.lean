module
public import Linear.IntegerGradedSubmoduleDecomposition
public import Linear.IntegerGradedSurjectionPreimage
public import Linear.IntegerGradedModuleGenerators
public import Mathlib.RingTheory.Noetherian.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {K S D E : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module K D] [Module S D] [IsScalarTower K S D]
variable [AddCommGroup E] [Module K E] [Module S E]
variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E)
variable [DirectSum.Decomposition 𝒟] [DirectSum.Decomposition ℰ]
variable (e : D →ₗ[S] E)
variable (hh : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d → e x ∈ ℰ d)
include hh

/-- The actual kernel of a degree-preserving map is closed under
actual homogeneous projections, rather than supplied as a graded kernel. -/
theorem integerDegreeZeroMap_kernel_isHomogeneous :
    (e.ker.restrictScalars K).IsHomogeneous 𝒟 := by
  intro d x hx
  change e (integerGradedModuleProjection 𝒟 d x) = 0
  change e x = 0 at hx
  rw [integerDegreeZeroMap_projection 𝒟 ℰ e hh, hx, map_zero]

/-- Over a noetherian original upper ring, the actual kernel has
finite homogeneous generators; the kernel grading and its finite
generation are both proved from the actual degree-preserving map. -/
theorem integerDegreeZeroMap_kernel_exists_homogeneous_generators
    [IsNoetherianRing S] [Module.Finite S D] :
    ∃ s : Finset e.ker, Submodule.span S (s : Set e.ker) = ⊤ ∧
      ∀ x ∈ s, ∃ d : ℤ, (x : D) ∈ 𝒟 d := by
  let p := e.ker.restrictScalars K
  let := integerGradedSubmoduleDecomposition 𝒟 p
    (integerDegreeZeroMap_kernel_isHomogeneous 𝒟 ℰ e hh)
  let : Module S p := inferInstanceAs (Module S e.ker)
  let : Module.Finite S p := inferInstanceAs (Module.Finite S e.ker)
  obtain ⟨s, hs, hh⟩ := integerGradedModule_exists_homogeneous_generators
    (A := S) (integerGradedSubmodulePiece 𝒟 p)
  exact ⟨s, hs, hh⟩

end LinearStudy
