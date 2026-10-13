module
public import Linear.NativeHomogeneousGlobalSection
public import Linear.NativeProjectiveTwistRegrading
public import Linear.NativeBaseSourceSectionsOverlap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] [SetLike.GradedSMul 𝒜 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- A degree-zero numerator in the ORIGINAL localized chart module. -/
def nativeHomogeneousZeroChartElement (d : ℕ) (a : R) (ell : 𝒟 0) :
    nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a :=
  ⟨LocalizedModule.mk (ell : M) 1,
    Submodule.subset_span ⟨0,(ell : M),by simpa using ell.property,by
      congr 1
      apply Subtype.ext
      simp⟩⟩

/-- Its actual chart section is the restriction of the SAME global
homogeneous fraction ell/1, not an independently chosen section. -/
theorem nativeHomogeneousZeroChartElement_section
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) (ell : 𝒟 0) :
    nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hR d a ha
      (nativeHomogeneousZeroChartElement 𝒜 𝒟 d a ell) =
    (nativeProjectiveModulePresheaf 𝒜 𝒟 hR 0).map (homOfLE le_top).op
      (nativeProjectiveModuleHomogeneousGlobalSection 𝒜 𝒟 hR 0 ell) := by
  apply Subtype.ext
  funext p
  change originalLocalizedModuleRefinement (Submonoid.powers a)
    p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2)
      (LocalizedModule.mk (ell : M) 1) = LocalizedModule.mk (ell : M) 1
  exact originalLocalizedModuleRefinement_mk_one (Submonoid.powers a)
    p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2) (ell : M)

/-- Base/source transport preserves the ORIGINAL global numerator and
unit denominator. The equality holds on every actual source chart. -/
theorem nativeHomogeneousZeroChartElement_source_section
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) (ell : 𝒟 0) :
    nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS d a ha
      (nativeHomogeneousZeroChartElement 𝒜 𝒟 d a ell) =
    (nativeProjectiveModulePresheaf 𝓑 𝒟 hS 0).map (homOfLE le_top).op
      (nativeProjectiveModuleHomogeneousGlobalSection 𝓑 𝒟 hS 0 ell) := by
  apply Subtype.ext
  funext p
  change nativeProjectiveChartRefinement 𝓑 (algebraMap R S a)
    (moduleBaseSourceLocalizationEquiv (S := S) a (LocalizedModule.mk (ell : M) 1)) p =
      LocalizedModule.mk (ell : M) 1
  rw [moduleBaseSourceLocalizationEquiv_mk_one]
  exact originalLocalizedModuleRefinement_mk_one (Submonoid.powers (algebraMap R S a))
    p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2) (ell : M)

/-- Regrading the actual homogeneous global section changes neither its
numerator nor any original prime-localized value. -/
theorem nativeHomogeneousGlobalSection_regrading (k : ℤ)
    (ell : integerGradingShift 𝒟 k 0) :
    nativeProjectiveTwistRegradingSectionEquiv 𝒜 𝒟 hR k (op ⊤)
      (nativeProjectiveModuleHomogeneousGlobalSection 𝒜 (integerGradingShift 𝒟 k)
        (integerGradingShift_smul_homogeneous 𝒜 𝒟 hR k) 0 ell) =
      nativeProjectiveModuleHomogeneousGlobalSection 𝒜 𝒟 hR k
        ⟨ell,by simpa only [integerGradingShift,zero_add] using ell.property⟩ := by
  apply Subtype.ext
  rfl
end LinearStudy
