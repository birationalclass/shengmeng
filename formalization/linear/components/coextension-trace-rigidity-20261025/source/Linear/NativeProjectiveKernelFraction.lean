module
public import Linear.IntegerGradedHomogeneousAnnihilator
public import Linear.NativeProjectiveKernelGrading
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

/-- A locally killed homogeneous fraction actually comes from a
homogeneous fraction in the original module kernel after shrinking
around any original projective point. -/
theorem nativeProjectiveKernelFraction_locally_lifts (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    {f : ∀ p : U, nativeProjectiveModuleAtPrime (D := E) 𝓑 p.1}
    (hf : nativeProjectiveModuleIsFraction 𝓑 ℰ k f)
    (hzero : ∀ p : U, nativeProjectiveModuleAtPrimeMap 𝓑 b p.1 (f p) = 0)
    (p : U) :
    ∃ (V : Opens (ProjectiveSpectrum.top 𝓑)) (hp : p.1 ∈ V) (i : V ⟶ U),
      ∃ g : ∀ q : V, nativeProjectiveModuleAtPrime (D := b.ker) 𝓑 q.1,
        nativeProjectiveModuleIsFraction 𝓑 (nativeProjectiveKernelPiece ℰ b) k g ∧
          ∀ q : V, nativeProjectiveModuleAtPrimeMap 𝓑 b.ker.subtype q.1 (g q) = f (i q) := by
  rcases hf with ⟨n, ell, den, hden, hf⟩
  have hz : LocalizedModule.mk (b (ell : E))
      (⟨(den : S), hden p⟩ : p.1.asHomogeneousIdeal.toIdeal.primeCompl) = 0 := by
    rw [← nativeProjectiveModuleAtPrimeMap_mk 𝓑 b p.1 ell ⟨den, hden p⟩,
      ← hf p]
    exact hzero p
  obtain ⟨m, c, hc, hcx⟩ := homogeneous_fraction_zero_has_homogeneous_annihilator
    𝓑 ℱ hF ((n : ℤ) + k) (b ell) (hh _ ell ell.property) p.1 ⟨den, hden p⟩ hz
  let V : Opens (ProjectiveSpectrum.top 𝓑) := U ⊓ ProjectiveSpectrum.basicOpen 𝓑 (c : S)
  have hp : p.1 ∈ V := ⟨p.property, hc⟩
  let i : V ⟶ U := homOfLE inf_le_left
  let num : b.ker := ⟨(c : S) • (ell : E), by
    change b ((c : S) • (ell : E)) = 0
    rw [map_smul]
    exact hcx⟩
  have hnum : num ∈ nativeProjectiveKernelPiece ℰ b (((n + m : ℕ) : ℤ) + k) := by
    change (c : S) • (ell : E) ∈ ℰ (((n + m : ℕ) : ℤ) + k)
    simpa only [Int.natCast_add, add_assoc, add_comm, add_left_comm]
      using hE m ((n : ℤ) + k) c c.property ell ell.property
  let denominator : 𝓑 (n + m) := ⟨(den : S) * (c : S),
    SetLike.mul_mem_graded den.property c.property⟩
  have hdenominator : ∀ q : V, (denominator : S) ∉ q.1.asHomogeneousIdeal := by
    intro q
    exact q.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hden (i q)) q.property.2
  let g : ∀ q : V, nativeProjectiveModuleAtPrime (D := b.ker) 𝓑 q.1 :=
    fun q => LocalizedModule.mk num ⟨denominator, hdenominator q⟩
  refine ⟨V, hp, i, g, ⟨n + m, ⟨num, hnum⟩, denominator, hdenominator, fun _ => rfl⟩, ?_⟩
  intro q
  dsimp only [g]
  rw [nativeProjectiveModuleAtPrimeMap_mk, hf (i q)]
  apply LocalizedModule.mk_eq.mpr
  refine ⟨1, ?_⟩
  simp [num, denominator, Submonoid.smul_def, smul_smul]

end LinearStudy
