module
public import Linear.BaseSourceLocalizedModuleInjective
public import Linear.NativeBaseSourceChartBijection
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] [SetLike.GradedSMul 𝒜 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable [IsDomain S] [Module.IsTorsionFree S M]
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- The pullback of the source's generic prime is an ACTUAL base Proj
point in every chart whose coordinate has nonzero source image. The
irrelevant-ideal condition follows from that same positive-degree coordinate. -/
def nativeBaseSourceGenericBaseChartPoint
    (d : ℕ) (hd : 0 < d) (a : R) (ha : a ∈ 𝒜 d)
    (hne : algebraMap R S a ≠ 0) : ProjectiveSpectrum.basicOpen 𝒜 a := by
  let f := normalizationBaseGradedRingHom 𝒜 𝓑
  let p : ProjectiveSpectrum 𝒜 := {
    asHomogeneousIdeal := (⊥ : HomogeneousIdeal 𝓑).comap f
    isPrime := by
      change (Ideal.comap f.toRingHom (⊥ : Ideal S)).IsPrime
      infer_instance
    not_irrelevant_le := by
      intro h
      have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd ha)
      change algebraMap R S a ∈ (⊥ : Ideal S) at hx
      exact hne (by simpa only [Submodule.mem_bot] using hx) }
  exact ⟨p,by
    change algebraMap R S a ∉ (⊥ : Ideal S)
    simpa only [Submodule.mem_bot] using hne⟩

include 𝓑 in
/-- The ACTUAL base chart-to-section map is injective for a module that
is torsion-free over the integral source. In particular the ambient
associated module of an integral quotient qualifies although it has base
torsion. Zero source coordinates are handled by the annihilation proof. -/
theorem nativeBaseSourceBaseChartDegreeZeroSectionMap_injective
    (d : ℕ) (hd : 0 < d) (a : R) (ha : a ∈ 𝒜 d) :
    Function.Injective (nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hR d a ha) := by
  by_cases hzero : algebraMap R S a = 0
  · letI := baseSourceAway_subsingleton_of_image_zero (M := M) a hzero
    intro x y _
    exact Subtype.ext (Subsingleton.elim x.val y.val)
  · let p := nativeBaseSourceGenericBaseChartPoint 𝒜 𝓑 d hd a ha hzero
    intro x y hxy
    apply Subtype.ext
    have hp := congrArg (fun z => z.val p) hxy
    let T := p.1.asHomogeneousIdeal.toIdeal.primeCompl
    change originalLocalizedModuleRefinement (Submonoid.powers a) T
        (Submonoid.powers_le.mpr p.2) x.val =
      originalLocalizedModuleRefinement (Submonoid.powers a) T
        (Submonoid.powers_le.mpr p.2) y.val at hp
    apply originalLocalizedModuleRefinement_injective_source_torsionFree (S := S)
      (Submonoid.powers a) T (Submonoid.powers_le.mpr p.2) _ hp
    intro t ht hz
    apply ht
    change algebraMap R S t ∈ (⊥ : Ideal S)
    simpa only [Submodule.mem_bot] using hz
end LinearStudy
