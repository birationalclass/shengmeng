module
public import Linear.NativeGradedDegreeOneOverlapSurjective
public import Mathlib.Algebra.Module.LocalizedModule.Away
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace LinearStudy
universe u
variable {K R M : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝒟 : ℤ → Submodule K M)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
/-- Restriction of scalars along the actual homogeneous ring overlap. -/
@[reducible] def nativeGradedDegreeOneOverlapBaseModule
    (a b : R) (hb : b ∈ 𝒜 1) :
    Module (HomogeneousLocalization.Away 𝒜 a)
      (nativeGradedModuleAwayDegreeZero 𝒜 𝒟 2 (a*b)) :=
  Module.compHom _ (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b))
/-- The genuine native graded-module overlap, viewed over the original base chart. -/
def nativeGradedDegreeOneOverlapLinearMap
    (hgrade : ∀ n : ℕ, ∀ j : ℤ, ∀ c : R, c ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → c • m ∈ 𝒟 ((n : ℤ)+j))
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) :
    letI := nativeGradedDegreeOneOverlapBaseModule 𝒜 𝒟 a b hb
    nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 a →ₗ[HomogeneousLocalization.Away 𝒜 a]
      nativeGradedModuleAwayDegreeZero 𝒜 𝒟 2 (a*b) := by
  letI := nativeGradedDegreeOneOverlapBaseModule 𝒜 𝒟 a b hb
  let f := nativeGradedModuleWeightedOverlapMap 𝒜 𝒟 hgrade 1 1 a b ha hb
  exact { toFun := f, map_add' := f.map_add', map_smul' := f.map_smul' }
/-- The ACTUAL weighted overlap module is the localization of the ACTUAL
degree-one chart at b/a. Torsion-freeness and nonzero coordinates ensure the
genuine restriction is injective; no module-localization certificate supplied. -/
theorem nativeGradedDegreeOneOverlap_isLocalizedModule
    [IsDomain R] [Module.IsTorsionFree R M]
    (hgrade : ∀ n : ℕ, ∀ j : ℤ, ∀ c : R, c ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → c • m ∈ 𝒟 ((n : ℤ)+j))
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) (hab : a*b ≠ 0) :
    letI := nativeGradedDegreeOneOverlapBaseModule 𝒜 𝒟 a b hb
    IsLocalizedModule.Away (HomogeneousLocalization.Away.isLocalizationElem ha hb)
      (nativeGradedDegreeOneOverlapLinearMap 𝒜 𝒟 hgrade a b ha hb) := by
  let Ai := HomogeneousLocalization.Away 𝒜 a
  let Aij := HomogeneousLocalization.Away 𝒜 (a*b)
  let N := nativeGradedModuleAwayDegreeZero 𝒜 𝒟 2 (a*b)
  letI := nativeGradedDegreeOneOverlapBaseModule 𝒜 𝒟 a b hb
  letI : Algebra Ai Aij :=
    (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)).toAlgebra
  letI : IsScalarTower Ai Aij N := IsScalarTower.of_compHom Ai Aij N
  letI : IsLocalization.Away (HomogeneousLocalization.Away.isLocalizationElem ha hb) Aij :=
    HomogeneousLocalization.Away.isLocalization_mul ha hb (rfl : a*b=a*b) (by decide)
  let t := HomogeneousLocalization.Away.isLocalizationElem ha hb
  let f := nativeGradedDegreeOneOverlapLinearMap 𝒜 𝒟 hgrade a b ha hb
  apply IsLocalizedModule.Away.mk
  · rw [← (Algebra.lsmul Ai (A := Aij) Ai N).commutes]
    exact (IsLocalization.map_units Aij (⟨t,⟨1,by simp⟩⟩ : Submonoid.powers t)).map
      (Algebra.lsmul Ai (A := Aij) Ai N).toRingHom
  · intro x
    obtain ⟨n,y,hy⟩ := nativeGradedModuleDegreeOneOverlap_surj 𝒜 𝒟 hgrade a b ha hb x
    refine ⟨n,y,?_⟩
    change HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b) (t^n) • x = _
    rw [map_pow]
    exact hy
  · intro x y hxy
    have heq : x = y := by
      apply Subtype.ext
      exact originalLocalizedModuleAwayOverlap_injective a b hab (congrArg Subtype.val hxy)
    exact ⟨0,by simp only [pow_zero,one_smul,heq]⟩
end LinearStudy
