module
public import Linear.NormalizationHomogeneousChartMap
public import Linear.CoextensionProjectiveGradeCompatibility
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
  nativeCoextensionNormalizationBaseModule

/-- The actual restricted original base-ring action on the native finite
dual preserves its original grading. This is derived from the actual
normalization map, not supplied as a compatibility certificate. -/
theorem coextensionNormalizationBaseGradeCompatibility :
    ∀ n : ℕ, ∀ d : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R),
        ell ∈ coextensionGradedPiece 𝒜 𝓑 d →
        b • ell ∈ coextensionGradedPiece 𝒜 𝓑 ((n : ℤ)+d) := by
  intro n d b hb ell hell
  have hs : algebraMap R S b ∈ 𝓑 n :=
    (normalizationBaseGradedRingHom 𝒜 𝓑).map_mem hb
  change algebraMap R S b • ell ∈ coextensionGradedPiece 𝒜 𝓑 ((n : ℤ)+d)
  exact coextensionProjectiveGradeCompatibility 𝒜 𝓑 n d (algebraMap R S b) hs ell hell
end LinearStudy
