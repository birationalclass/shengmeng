module
public import Linear.NativeProjectiveModuleSheafMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S D E : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable [AddCommGroup E] [Module S E] [Module K E]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E)
variable (e : D →ₗ[S] E)

/-- If actual homogeneous numerators have homogeneous preimages, then
every actual homogeneous fraction lifts on the same original open.
The denominator and the open are preserved exactly. -/
theorem nativeProjectiveModuleFraction_lifts
    (hpre : ∀ d : ℤ, ∀ ell : E, ell ∈ ℰ d →
      ∃ x : D, x ∈ 𝒟 d ∧ e x = ell)
    (k : ℤ) {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := E) 𝓑 p.1}
    (hf : nativeProjectiveModuleIsFraction 𝓑 ℰ k f) :
    ∃ g : ∀ p : U, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1,
      nativeProjectiveModuleIsFraction 𝓑 𝒟 k g ∧
      ∀ p : U, nativeProjectiveModuleAtPrimeMap 𝓑 e p.1 (g p) = f p := by
  rcases hf with ⟨n,ell,b,hb,hf⟩
  obtain ⟨x,hx,hex⟩ := hpre ((n : ℤ)+k) ell ell.property
  let g : ∀ p : U, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1 :=
    fun p => LocalizedModule.mk x ⟨b,hb p⟩
  refine ⟨g,⟨n,⟨x,hx⟩,b,hb,fun _ => rfl⟩,?_⟩
  intro p
  dsimp only [g]
  rw [nativeProjectiveModuleAtPrimeMap_mk,hex]
  exact (hf p).symm

end LinearStudy
