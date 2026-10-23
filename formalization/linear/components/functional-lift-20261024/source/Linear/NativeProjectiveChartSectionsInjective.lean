module
public import Linear.NativeProjectiveChartSections
public import Mathlib.Algebra.Module.Torsion.Free
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R M : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]

/-- Localizing a torsion-free module over a domain further at nonzero
denominators loses no elements. This supplies actual pointwise separation. -/
theorem originalLocalizedModuleRefinement_injective
    [IsDomain R] [Module.IsTorsionFree R M]
    (P T : Submonoid R) (hPT : P ≤ T) (hT : ∀ t ∈ T, t ≠ 0) :
    Function.Injective (originalLocalizedModuleRefinement (M := M) P T hPT) := by
  apply IsLocalizedModule.injective_of_map_zero P (LocalizedModule.mkLinearMap P M)
  intro m hm
  change originalLocalizedModuleRefinement P T hPT (LocalizedModule.mk m 1) = 0 at hm
  rw [originalLocalizedModuleRefinement_mk_one] at hm
  have hz : LocalizedModule.mkLinearMap T M m = 0 := hm
  obtain ⟨t,ht⟩ := (IsLocalizedModule.eq_zero_iff T (LocalizedModule.mkLinearMap T M)).mp hz
  have hm0 : m = 0 := (smul_eq_zero_iff_right (hT t.val t.property)).mp ht
  simp [hm0]

variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝒟 : ℤ → Submodule K M)
variable (hgrade : ∀ n : ℕ, ∀ j : ℤ, ∀ a : R, a ∈ 𝒜 n →
  ∀ m : M, m ∈ 𝒟 j → a • m ∈ 𝒟 ((n : ℤ)+j))
attribute [local instance] LocalizedModule.moduleOfIsLocalization
  nativeHomogeneousAwayModuleScalar nativeProjectiveAtPrimeModuleScalar
  nativeProjectiveAmbientSectionModule

/-- A nonzero positive-degree coordinate constructs the actual generic
point in its original Proj basic open. No nonempty-chart input is needed. -/
def nativeProjectiveGenericChartPoint [IsDomain R]
    (d : ℕ) (hd : 0 < d) (a : R) (ha : a ∈ 𝒜 d) (hne : a ≠ 0) :
    ProjectiveSpectrum.basicOpen 𝒜 a := by
  let p : ProjectiveSpectrum 𝒜 := {
    asHomogeneousIdeal := ⊥
    isPrime := by simpa only [HomogeneousIdeal.toIdeal_bot] using (inferInstance : (⊥ : Ideal R).IsPrime)
    not_irrelevant_le := by
      intro h
      have hmem := h (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd ha)
      exact hne (by change a ∈ (⊥ : Ideal R) at hmem; simpa using hmem) }
  exact ⟨p,by change a ∉ (⊥ : Ideal R); simpa using hne⟩

/-- For a torsion-free module on an integral graded domain, the actual
positive-degree chart-to-section map is injective, detected at the
constructed original generic point. Surjectivity is a separate obligation. -/
theorem nativeProjectiveChartDegreeZeroSectionMap_injective
    [IsDomain R] [Module.IsTorsionFree R M]
    (d : ℕ) (hd : 0 < d) (a : R) (ha : a ∈ 𝒜 d) (hne : a ≠ 0) :
    Function.Injective (nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hgrade d a ha) := by
  let p := nativeProjectiveGenericChartPoint 𝒜 d hd a ha hne
  intro x y hxy
  apply Subtype.ext
  have hp : nativeProjectiveChartRefinement 𝒜 a x.val p =
      nativeProjectiveChartRefinement 𝒜 a y.val p :=
    congrArg (fun s => s.val p) hxy
  change originalLocalizedModuleRefinement (Submonoid.powers a)
      p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2) x.val =
    originalLocalizedModuleRefinement (Submonoid.powers a)
      p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2) y.val at hp
  apply originalLocalizedModuleRefinement_injective (Submonoid.powers a)
    p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2) _ hp
  intro t ht
  exact fun hz => ht (hz ▸ Ideal.zero_mem _)

end LinearStudy
