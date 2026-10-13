module
public import Linear.NativeProjectiveModulePresheaf
public import Mathlib.Topology.Sheaves.Forget
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S D : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D)
variable (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))

/-- The homogeneous local-fraction presheaf satisfies the sheaf condition
for the ORIGINAL Proj topology, with its native structure-ring action. -/
theorem nativeProjectiveModulePresheaf_isSheaf (k : ℤ) :
    TopCat.Presheaf.IsSheaf
      (nativeProjectiveModulePresheaf 𝓑 𝒟 hgrade k).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)
    (nativeProjectiveModulePresheaf 𝓑 𝒟 hgrade k).presheaf).mpr
  exact TopCat.Presheaf.isSheaf_of_iso
    (nativeProjectiveModulePresheafForgetIso 𝓑 𝒟 hgrade k).symm
    (nativeProjectiveModuleSheafInType 𝓑 𝒟 k).property

/-- Actual associated homogeneous module sheaf on mathlib's native Proj.
No sheaf, local-fraction model, or sheaf-condition certificate is an input. -/
def nativeProjectiveModuleSheaf (k : ℤ) : (AlgebraicGeometry.Proj 𝓑).Modules where
  val := nativeProjectiveModulePresheaf 𝓑 𝒟 hgrade k
  isSheaf := nativeProjectiveModulePresheaf_isSheaf 𝓑 𝒟 hgrade k

end LinearStudy
