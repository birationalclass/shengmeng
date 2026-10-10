module
public import Linear.NativeProjectiveChartSections
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
variable {K S M N : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable [AddCommGroup N] [Module K N] [Module S N]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local instance] LocalizedModule.moduleOfIsLocalization
  nativeHomogeneousAwayModuleScalar nativeProjectiveAtPrimeModuleScalar
  nativeProjectiveAmbientSectionModule

/-- Original module maps commute with actual refinement from a chart
localization to the original projective prime. -/
theorem nativeProjectiveChartRefinement_moduleMap
    (e : M →ₗ[S] N) (a : S)
    (x : LocalizedModule (Submonoid.powers a) M)
    (p : ProjectiveSpectrum.basicOpen 𝓑 a) :
    nativeProjectiveChartRefinement 𝓑 a
      (LocalizedModule.map (Submonoid.powers a) e x) p =
      nativeProjectiveModuleAtPrimeMap 𝓑 e p.1
        (nativeProjectiveChartRefinement 𝓑 a x p) := by
  induction x using LocalizedModule.induction_on with
  | h m b =>
    dsimp only [nativeProjectiveChartRefinement]
    rw [LocalizedModule.map_mk, originalLocalizedModuleRefinement_mk,
      originalLocalizedModuleRefinement_mk,nativeProjectiveModuleAtPrimeMap_mk]

/-- An original degree-zero homogeneous module map preserves the
actual degree-zero chart module, including its sums and chart scalars. -/
theorem nativeGradedModuleAwayDegreeZero_moduleMap_mem
    (𝒟 : ℤ → Submodule K M) (ℰ : ℤ → Submodule K N)
    (e : M →ₗ[S] N) (hh : ∀ d : ℤ, ∀ m : M, m ∈ 𝒟 d → e m ∈ ℰ (d+0))
    (d : ℕ) (a : S) (x : LocalizedModule (Submonoid.powers a) M)
    (hx : x ∈ nativeGradedModuleAwayDegreeZero 𝓑 𝒟 d a) :
    LocalizedModule.map (Submonoid.powers a) e x ∈
      nativeGradedModuleAwayDegreeZero 𝓑 ℰ d a := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n,m,hm,rfl⟩ := hz
    rw [LocalizedModule.map_mk]
    apply Submodule.subset_span
    exact ⟨n,e m,by simpa only [add_zero] using hh ((n*d : ℕ) : ℤ) m hm,rfl⟩
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    change LocalizedModule.map (Submonoid.powers a) e (c.val • x) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

end LinearStudy
