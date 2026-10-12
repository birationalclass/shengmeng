module
public import Linear.NativeProjectiveDegreeZeroEpi
public import Linear.SchemeModuleKernelHOneSectionLift
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u w
variable {K S D E : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable [AddCommGroup E] [Module S E] [Module K E]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E)
variable [DirectSum.Decomposition 𝒟] [DirectSum.Decomposition ℰ]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : D, x ∈ 𝒟 d → b • x ∈ 𝒟 ((n : ℤ) + d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → b • x ∈ ℰ ((n : ℤ) + d))
variable (e : D →ₗ[S] E)
variable (hh : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d → e x ∈ ℰ d)

/-- Let e be an ACTUAL surjective homogeneous graded-module map and fix k.
Then H1 of the ACTUAL kernel of its associated sheaf map gives a lift of
EVERY actual degree-k global section. The sheaf epimorphism and its kernel
short exact sequence are derived from e, not assumed as certificates.
This is the native projective specialization required for the next ideal
sheaf step in original4.2. Eventual H1 vanishing and identification of
ambient global sections with homogeneous polynomials remain OPEN. -/
theorem nativeProjectiveDegreeZeroSheafMap_sections_surjective_of_kernel_H1_vanish
    (he : Function.Surjective e) (k : ℤ)
    [HasExt.{w} (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (AlgebraicGeometry.Proj 𝓑)) AddCommGrpCat.{u})]
    [Subsingleton (CategoryTheory.Sheaf.H.{w}
      ((schemeModuleToAdditiveSheaf (AlgebraicGeometry.Proj 𝓑)).obj
        (kernel (nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE e hh k))) 1)] :
    Function.Surjective
      ((nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE e hh k).app ⊤) := by
  letI : Epi (nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE e hh k) :=
    nativeProjectiveDegreeZeroSheafMap_epi 𝓑 𝒟 ℰ hD hE e hh he k
  exact schemeModuleEpi_sections_surjective_of_kernel_H1_vanish
    (nativeProjectiveDegreeZeroSheafMap 𝓑 𝒟 ℰ hD hE e hh k)
end LinearStudy
