module
public import Linear.NativeProjectiveTwistFinitePresentation
public import Linear.NativeProjectiveFiniteGradedFinitePresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ c : S, c ∈ 𝓑 n →
  ∀ x : M, x ∈ 𝒟 d → c • x ∈ 𝒟 ((n : ℤ)+d))

/-- Every ORIGINAL integer-twist associated-module sheaf is genuinely
quasicoherent,derived from its actual finite presentation and original
coordinate cover. No quasicoherence or local H input is assumed. -/
theorem nativeFiniteGradedTwist_isQuasicoherent_of_cover
    [IsNoetherianRing S] [Module.Finite S M] (k : ℤ) {ι : Type u}
    (a : ι → S) (ha : ∀ i,a i ∈ 𝓑 1)
    (hcover : (⨆ i,Proj.basicOpen 𝓑 (a i)) = ⊤) :
    (nativeProjectiveModuleSheaf 𝓑 𝒟 hD k).IsQuasicoherent := by
  letI : (nativeProjectiveModuleSheaf 𝓑 𝒟 hD k).IsFinitePresentation :=
    nativeFiniteGradedTwist_isFinitePresentation_of_cover 𝓑 𝒟 hD k a ha hcover
  infer_instance
end LinearStudy
