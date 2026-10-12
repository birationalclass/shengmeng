module
public import Linear.IntegerGradedModuleProjection
public import Linear.NativeProjectiveModuleLocalPredicate
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry
variable {K S E : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup E] [Module K E] [Module S E]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (ℰ : ℤ → Submodule K E) [DirectSum.Decomposition ℰ]
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ x : E, x ∈ ℰ d → b • x ∈ ℰ ((n : ℤ) + d))
include hE

/-- A homogeneous module element shifts the actual ring projections,
even when its own degree is negative. -/
theorem ringProjection_smul_integerHomogeneous (d : ℤ) (x : E) (hx : x ∈ ℰ d)
    (n : ℕ) (b : S) :
    gradedModuleProjection 𝓑 n b • x =
      integerGradedModuleProjection ℰ ((n : ℤ) + d) (b • x) := by
  induction b using DirectSum.Decomposition.inductionOn 𝓑 with
  | zero => simp
  | @homogeneous j b =>
    rw [gradedModuleProjection_on_piece 𝓑 n j b b.property,
      integerGradedModuleProjection_on_piece ℰ ((n : ℤ) + d) ((j : ℤ) + d)
        ((b : S) • x) (hE j d (b : S) b.property x hx)]
    have hiff : (n : ℤ) + d = (j : ℤ) + d ↔ n = j := by omega
    simp only [hiff]
    split_ifs <;> simp
  | add b c hb hc => simp only [map_add, add_smul, hb, hc]

/-- Each homogeneous component of an actual annihilator still
annihilates the homogeneous element; this is derived from projections. -/
theorem ringProjection_smul_eq_zero (d : ℤ) (x : E) (hx : x ∈ ℰ d)
    (b : S) (hb : b • x = 0) (n : ℕ) :
    gradedModuleProjection 𝓑 n b • x = 0 := by
  rw [ringProjection_smul_integerHomogeneous 𝓑 ℰ hE d x hx n b, hb, map_zero]

/-- A homogeneous element killed after prime localization has an
ACTUAL homogeneous annihilator outside that original homogeneous prime.
The homogeneous annihilator is constructed from a component of the
ordinary localization witness, not assumed as additional data. -/
theorem homogeneous_annihilator_outside_projectivePrime (d : ℤ)
    (x : E) (hx : x ∈ ℰ d) (p : ProjectiveSpectrum 𝓑)
    (b : S) (hb : b ∉ p.asHomogeneousIdeal) (hbx : b • x = 0) :
    ∃ n : ℕ, ∃ c : 𝓑 n, (c : S) ∉ p.asHomogeneousIdeal ∧ (c : S) • x = 0 := by
  classical
  have hn : ∃ n : ℕ, (DirectSum.decompose 𝓑 b n : S) ∉ p.asHomogeneousIdeal := by
    by_contra h
    push Not at h
    apply hb
    rw [← DirectSum.sum_support_decompose 𝓑 b]
    exact p.asHomogeneousIdeal.toIdeal.sum_mem fun n hn => h n
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, DirectSum.decompose 𝓑 b n, hn, ?_⟩
  exact ringProjection_smul_eq_zero 𝓑 ℰ hE d x hx b hbx n

/-- Vanishing of an actual homogeneous fraction produces a homogeneous
annihilator outside its original projective prime. -/
theorem homogeneous_fraction_zero_has_homogeneous_annihilator (d : ℤ)
    (x : E) (hx : x ∈ ℰ d) (p : ProjectiveSpectrum 𝓑)
    (b : p.asHomogeneousIdeal.toIdeal.primeCompl)
    (hz : LocalizedModule.mk x b = 0) :
    ∃ n : ℕ, ∃ c : 𝓑 n, (c : S) ∉ p.asHomogeneousIdeal ∧ (c : S) • x = 0 := by
  have hzero : LocalizedModule.mk x b =
      LocalizedModule.mk (0 : E) (1 : p.asHomogeneousIdeal.toIdeal.primeCompl) := by
    simpa only [LocalizedModule.zero_mk] using hz
  obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp hzero
  have hc0 : (c : S) • x = 0 := by
    simpa only [one_smul, smul_zero, Submonoid.smul_def] using hc
  exact homogeneous_annihilator_outside_projectivePrime 𝓑 ℰ hE d x hx p c c.property hc0

end LinearStudy
