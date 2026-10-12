module
public import Linear.FiniteCoextensionUpperModule
public import Linear.CoextensionGradedModule
public import Linear.IntegerGradedModuleGenerators
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
variable [SetLike.GradedSMul 𝒜 𝓑] [IsNoetherianRing R] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule

/-- The actual native normalization dual has finite homogeneous
generators over the original upper ring; both its integer grading and
its upper-ring finiteness are constructed from the original finite map. -/
theorem nativeCoextensionDual_exists_homogeneous_generators :
    ∃ s : Finset ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)),
      Submodule.span S
        (s : Set ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) = ⊤ ∧
        ∀ ell ∈ s, ∃ d : ℤ, ell ∈ coextensionGradedPiece 𝒜 𝓑 d := by
  let := coextensionGradedDecomposition 𝒜 𝓑
  let := nativeCoextensionDual_finite_upper (R := R) (S := S)
  exact integerGradedModule_exists_homogeneous_generators (A := S)
    (coextensionGradedPiece 𝒜 𝓑)

end LinearStudy
