module
public import Linear.NativeBaseSourceChartBijection
public import Linear.NativeWeightedOverlapTarget
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K S M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] [SetLike.GradedSMul 𝒜 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable [IsDomain S] [Module.IsTorsionFree S M]
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
attribute [local irreducible] nativeBaseSourceWeightedChartSection nativeGradedModuleWeightedOverlapMap
  nativeProjectiveChartDegreeZeroSectionMap nativeGradedModuleWeightedOverlapTo

/-- Source global sections determine compatible ORIGINAL base-chart
fractions. Actual weighted restriction and source chart injectivity prove
the overlap equality, even when one coordinate has zero image. -/
theorem nativeBaseSourceChartSection_overlap_agrees
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 a)
    (y : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 b)
    (s : Γ(nativeProjectiveModuleSheaf 𝓑 𝒟 hS 0,⊤))
    (hx : nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS 1 a ha x =
      (nativeProjectiveModulePresheaf 𝓑 𝒟 hS 0).map (homOfLE le_top).op s)
    (hy : nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS 1 b hb y =
      (nativeProjectiveModulePresheaf 𝓑 𝒟 hS 0).map (homOfLE le_top).op s) :
    (nativeProjectiveModulePresheaf 𝒜 𝒟 hR 0).map
      (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)).op
        (nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hR 1 a ha x) =
    (nativeProjectiveModulePresheaf 𝒜 𝒟 hR 0).map
      (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_right 𝒜 a b)).op
        (nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hR 1 b hb y) := by
  let l := nativeGradedModuleWeightedOverlapTo 𝒜 𝒟 hR 1 1 a b (a*b) ha hb rfl x
  let r := nativeGradedModuleWeightedOverlapTo 𝒜 𝒟 hR 1 1 b a (a*b) hb ha (mul_comm a b) y
  have hlA := nativeProjectiveChartDegreeZeroSectionMap_overlap_to
    𝒜 𝒟 hR 1 1 a b (a*b) ha hb rfl x
  have hrA : (nativeProjectiveModulePresheaf 𝒜 𝒟 hR 0).map
      (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_right 𝒜 a b)).op
        (nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hR 1 b hb y) =
      nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hR 2 (a*b)
        (SetLike.mul_mem_graded ha hb) r := by
    exact nativeProjectiveChartDegreeZeroSectionMap_overlap_to
      𝒜 𝒟 hR 1 1 b a (a*b) hb ha (mul_comm a b) y
  have hrS : (nativeProjectiveModulePresheaf 𝓑 𝒟 hS 0).map
      (homOfLE (show Proj.basicOpen 𝓑 (algebraMap R S (a*b)) ≤
        Proj.basicOpen 𝓑 (algebraMap R S b) from by
          rw [map_mul]; exact ProjectiveSpectrum.basicOpen_mul_le_right 𝓑 _ _)).op
        (nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS 1 b hb y) =
      nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS 2 (a*b)
        (SetLike.mul_mem_graded ha hb) r := by
    exact nativeBaseSourceWeightedChartSection_overlap_to
      𝒜 𝓑 𝒟 hR hS 1 1 b a (a*b) hb ha (mul_comm a b) y
  have hlS := nativeBaseSourceWeightedChartSection_overlap_to
    𝒜 𝓑 𝒟 hR hS 1 1 a b (a*b) ha hb rfl x
  have hxy : l = r := by
    apply nativeBaseSourceWeightedChartSection_injective 𝒜 𝓑 𝒟 hR hS 2 (by decide)
      (a*b) (SetLike.mul_mem_graded ha hb)
    rw [← hlS,← hrS,hx,hy]
    let B := nativeProjectiveModuleSheaf 𝓑 𝒟 hS 0
    change B.presheaf.map (homOfLE _).op (B.presheaf.map (homOfLE _).op s) =
      B.presheaf.map (homOfLE _).op (B.presheaf.map (homOfLE _).op s)
    rw [← ConcreteCategory.comp_apply,← Functor.map_comp,
      ← ConcreteCategory.comp_apply,← Functor.map_comp]
    congr 1
  exact hlA.trans ((congrArg (nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hR 2 (a*b)
    (SetLike.mul_mem_graded ha hb)) hxy).trans hrA.symm)
end LinearStudy
