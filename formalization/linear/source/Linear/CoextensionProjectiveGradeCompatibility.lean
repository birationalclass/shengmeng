module
public import Linear.NativeProjectiveRingIntegerPieces
public import Linear.CoextensionGradedModule
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] coextensionGradedBaseModule

/-- The actual finite-normalization dual grading satisfies precisely
the compatibility needed to construct its native Proj module sheaf. -/
theorem coextensionProjectiveGradeCompatibility :
    ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
      ∀ ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R),
        ell ∈ coextensionGradedPiece 𝒜 𝓑 d →
        b • ell ∈ coextensionGradedPiece 𝒜 𝓑 ((n : ℤ)+d) := by
  intro n d b hb ell hell
  simpa only [add_comm] using
    coextensionGradedPiece_smul_homogeneous 𝒜 𝓑 n d b hb ell hell

end LinearStudy
