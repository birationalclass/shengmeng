module
public import Linear.CoextensionGradedModule
public import Linear.CoextensionHomInjective
public import Linear.IntegerDomainHomComponentNonzero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [CommRing S] [IsDomain S] [Algebra K R] [Algebra K S] [Algebra R S]
variable [IsScalarTower K R S] [FaithfulSMul R S] [Module.Finite R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] coextensionGradedBaseModule

/-- Construct an ACTUAL homogeneous linear injection of the native
normalization dual into the upper ring, with one integer shift.
The map and the shift are chosen from the actual ungraded embedding. -/
theorem coextensionDual_exists_homogeneous_embedding :
    ∃ k : ℤ, ∃ e : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R) →ₗ[S] S,
      Function.Injective e ∧ ∀ d : ℤ, ∀ ell,
        ell ∈ coextensionGradedPiece 𝒜 𝓑 d →
        e ell = gradedIntegerProjection 𝓑 (d+k) (e ell) := by
  let D := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  letI : IsScalarTower K S D := IsScalarTower.of_compHom K S D
  letI := coextensionGradedDecomposition 𝒜 𝓑
  have hgrade : ∀ d : ℕ, ∀ b : S, b ∈ 𝓑 d → ∀ j : ℤ, ∀ ell : D,
      ell ∈ 𝒟 j → b • ell ∈ 𝒟 (j+(d : ℤ)) := by
    intro d b hb j ell hell
    exact coextensionGradedPiece_smul_homogeneous 𝒜 𝓑 d j b hb ell hell
  obtain ⟨e,he⟩ := coextensionDual_exists_integral_embedding (R := R) (S := S)
  by_cases hz : e = 0
  · refine ⟨0,e,he,?_⟩
    intro d ell hell
    simp only [hz,LinearMap.zero_apply,map_zero]
  · obtain ⟨k,hk⟩ := integerDomainHomComponent_exists_nonzero 𝓑 𝒟 𝓑 hgrade e hz
    let g := integerDomainHomComponent 𝓑 𝒟 𝓑 hgrade e k
    refine ⟨k,g,coextensionDual_nonzero_linear_map_injective g hk,?_⟩
    intro d ell hell
    exact integerDomainHomComponent_homogeneous 𝓑 𝒟 𝓑 hgrade e k d ell hell

end LinearStudy
