module
public import Linear.NativeProjectiveKernelFraction
public import Linear.NativeProjectivePrimeMapExact
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

/-- A native associated-module section killed by the actual map lifts
on the SAME whole open to an actual kernel section. Prime-local lifts
are unique; homogeneous local fractions prove their local regularity. -/
theorem nativeProjectiveKernelLocalPredicate_lifts (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := E) 𝓑 p.1}
    (hf : (nativeProjectiveModuleLocalPredicate 𝓑 ℰ k).pred f)
    (hzero : ∀ p : U, nativeProjectiveModuleAtPrimeMap 𝓑 b p.1 (f p) = 0) :
    ∃ g : ∀ p : U, nativeProjectiveModuleAtPrime (D := b.ker) 𝓑 p.1,
      (nativeProjectiveModuleLocalPredicate 𝓑 (nativeProjectiveKernelPiece ℰ b) k).pred g ∧
        ∀ p : U, nativeProjectiveModuleAtPrimeMap 𝓑 b.ker.subtype p.1 (g p) = f p := by
  classical
  have hex := LinearMap.exact_subtype_ker_map b
  have hlift : ∀ p : U, ∃ x : nativeProjectiveModuleAtPrime (D := b.ker) 𝓑 p.1,
      nativeProjectiveModuleAtPrimeMap 𝓑 b.ker.subtype p.1 x = f p := by
    intro p
    exact (nativeProjectiveModuleAtPrimeMap_exact 𝓑 b.ker.subtype b hex p.1
      (f p)).mp (hzero p)
  let g : ∀ p : U, nativeProjectiveModuleAtPrime (D := b.ker) 𝓑 p.1 :=
    fun p => Classical.choose (hlift p)
  have hg : ∀ p : U, nativeProjectiveModuleAtPrimeMap 𝓑 b.ker.subtype p.1 (g p) = f p :=
    fun p => Classical.choose_spec (hlift p)
  refine ⟨g, ?_, hg⟩
  intro p
  obtain ⟨V, hp, i, hfrac⟩ := hf p
  obtain ⟨W, hpW, j, g', hfrac', hmap⟩ :=
    nativeProjectiveKernelFraction_locally_lifts 𝓑 ℰ ℱ hE hF b hh k hfrac
      (fun q => hzero (i q)) ⟨p.1, hp⟩
  refine ⟨W, hpW, j ≫ i, ?_⟩
  have heq : (fun q : W => g ((j ≫ i) q)) = g' := by
    funext q
    apply nativeProjectiveModuleAtPrimeMap_injective 𝓑 b.ker.subtype
      b.ker.subtype_injective q.1
    exact (hg ((j ≫ i) q)).trans (hmap q).symm
  change nativeProjectiveModuleIsFraction 𝓑 (nativeProjectiveKernelPiece ℰ b) k
    (fun q : W => g ((j ≫ i) q))
  rw [heq]
  exact hfrac'

end LinearStudy
