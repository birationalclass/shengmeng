module
public import Linear.NativeProjectiveKernelLocalLift
public import Linear.NativeProjectiveDegreeZeroMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
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

/-- Exactness of the actual kernel inclusion and original degree-zero
map on sections over EVERY original open, derived from actual homogeneous
fraction lifts. This supplies the objectwise kernel comparison. -/
theorem nativeProjectiveKernelSectionMap_exact (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ) :
    let hK := nativeProjectiveKernelPiece_graded 𝓑 ℰ b hE
    Function.Exact
      (nativeProjectiveDegreeZeroSectionMap 𝓑 (nativeProjectiveKernelPiece ℰ b) ℰ
        hK hE b.ker.subtype (fun _ _ hx => hx) k U)
      (nativeProjectiveDegreeZeroSectionMap 𝓑 ℰ ℱ hE hF b hh k U) := by
  dsimp only
  intro f
  constructor
  · intro hzero
    have hz : ∀ p : U.unop, nativeProjectiveModuleAtPrimeMap 𝓑 b p.1 (f.1 p) = 0 := by
      intro p
      exact congrArg (fun t => t.1 p) hzero
    obtain ⟨g, hg, hmap⟩ := nativeProjectiveKernelLocalPredicate_lifts
      𝓑 ℰ ℱ hE hF b hh k f.property hz
    refine ⟨⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    funext p
    exact hmap p
  · rintro ⟨g, rfl⟩
    apply Subtype.ext
    funext p
    exact (nativeProjectiveModuleAtPrimeMap_exact 𝓑 b.ker.subtype b
      (LinearMap.exact_subtype_ker_map b) p.1).apply_apply_eq_zero (g.1 p)

end LinearStudy
