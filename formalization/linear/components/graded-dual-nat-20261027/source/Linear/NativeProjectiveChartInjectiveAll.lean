module
public import Linear.NativeProjectiveChartSectionsInjective
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
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ j : ℤ, ∀ a : R, a ∈ 𝒜 n →
  ∀ m : M, m ∈ 𝒟 j → a • m ∈ 𝒟 ((n : ℤ)+j))
attribute [local instance] LocalizedModule.moduleOfIsLocalization
  nativeHomogeneousAwayModuleScalar nativeProjectiveAtPrimeModuleScalar
  nativeProjectiveAmbientSectionModule

/-- The zero-coordinate chart is harmless: its actual localized module
is zero. This does not impose nonvanishing of every coordinate on a variety. -/
theorem nativeProjectiveZeroChartSectionMap_injective
    (d : ℕ) (ha : (0 : R) ∈ 𝒜 d) :
    Function.Injective (nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hD d 0 ha) := by
  letI : Subsingleton (LocalizedModule (Submonoid.powers (0 : R)) M) :=
    LocalizedModule.subsingleton (Submonoid.mem_powers 0)
  intro x y _
  exact Subtype.ext (Subsingleton.elim x.val y.val)

/-- On an integral source, every positive-degree weighted chart map is
injective, including empty charts. Only source torsion-freeness is used. -/
theorem nativeProjectiveChartDegreeZeroSectionMap_injective_all
    [IsDomain R] [Module.IsTorsionFree R M]
    (d : ℕ) (hd : 0 < d) (a : R) (ha : a ∈ 𝒜 d) :
    Function.Injective (nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hD d a ha) := by
  by_cases h : a = 0
  · subst a
    exact nativeProjectiveZeroChartSectionMap_injective 𝒜 𝒟 hD d ha
  · exact nativeProjectiveChartDegreeZeroSectionMap_injective 𝒜 𝒟 hD d hd a ha h
end LinearStudy
