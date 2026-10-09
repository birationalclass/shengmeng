module
public import Linear.NativeProjectiveKernelSectionExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite Limits
universe u
variable {K S E F : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup E] [Module K E] [Module S E] [IsScalarTower K S E]
variable [AddCommGroup F] [Module K F] [Module S F]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (ℰ : ℤ → Submodule K E) (ℱ : ℤ → Submodule K F)
variable [DirectSum.Decomposition ℱ]
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → c • x ∈ ℰ ((n : ℤ) + d))
variable (hF : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : F, x ∈ ℱ d → c • x ∈ ℱ ((n : ℤ) + d))
variable (b : E →ₗ[S] F)
variable (hh : ∀ d : ℤ, ∀ x : E, x ∈ ℰ d → b x ∈ ℱ d)
include hE hF hh

/-- The actual native associated-sheaf inclusion of the actual module
kernel into the original source. -/
def nativeProjectiveKernelSheafInclusion (k : ℤ) :
    nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveKernelPiece ℰ b)
      (nativeProjectiveKernelPiece_graded 𝓑 ℰ b hE) k ⟶
        nativeProjectiveModuleSheaf 𝓑 ℰ hE k :=
  nativeProjectiveDegreeZeroSheafMap 𝓑 (nativeProjectiveKernelPiece ℰ b) ℰ
    (nativeProjectiveKernelPiece_graded 𝓑 ℰ b hE) hE b.ker.subtype
      (fun _ _ hx => hx) k

theorem nativeProjectiveKernelSheafInclusion_comp_zero (k : ℤ) :
    nativeProjectiveKernelSheafInclusion 𝓑 ℰ hE b k ≫
      nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hh k = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (nativeProjectiveKernelSectionMap_exact 𝓑 ℰ ℱ hE hF b hh k U).apply_apply_eq_zero x

/-- The native associated sheaf of the ACTUAL graded kernel has the
categorical kernel universal property. Objectwise kernel exactness is
proved above, and genuine sheaf evaluation/forgetful limit reflection is
reused from pinned mathlib. -/
def nativeProjectiveKernelSheafIsLimit (k : ℤ) :
    IsLimit (KernelFork.ofι (nativeProjectiveKernelSheafInclusion 𝓑 ℰ hE b k)
      (nativeProjectiveKernelSheafInclusion_comp_zero 𝓑 ℰ ℱ hE hF b hh k)) := by
  let R := (AlgebraicGeometry.Proj 𝓑).ringCatSheaf
  let i := nativeProjectiveKernelSheafInclusion 𝓑 ℰ hE b k
  let β := nativeProjectiveDegreeZeroSheafMap 𝓑 ℰ ℱ hE hF b hh k
  let w : i ≫ β = 0 := nativeProjectiveKernelSheafInclusion_comp_zero 𝓑 ℰ ℱ hE hF b hh k
  let c := KernelFork.ofι i w
  apply isLimitOfReflects (SheafOfModules.forget R)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  change IsLimit (((SheafOfModules.forget R) ⋙ (PresheafOfModules.evaluation R.obj U)).mapCone c)
  refine (isLimitMapConeForkEquiv'
    ((SheafOfModules.forget R) ⋙ (PresheafOfModules.evaluation R.obj U)) w).symm ?_
  exact ModuleCat.isLimitKernelFork _ _
    (nativeProjectiveKernelSectionMap_exact 𝓑 ℰ ℱ hE hF b hh k U)
    (nativeProjectiveDegreeZeroSectionMap_injective 𝓑
      (nativeProjectiveKernelPiece ℰ b) ℰ
      (nativeProjectiveKernelPiece_graded 𝓑 ℰ b hE) hE b.ker.subtype
      (fun _ _ hx => hx) b.ker.subtype_injective k U)

end LinearStudy
