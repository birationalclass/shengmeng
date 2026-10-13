module
public import Linear.NativeBaseSourceBaseChartInjective
public import Linear.NativeHomogeneousZeroChartSection
public import Linear.NativeProjectiveDegreeOneCover
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
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
variable [IsDomain S] [Module.IsTorsionFree S M]
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- The actual base/source lifting comparison preserves a homogeneous
global fraction. If the base lift is ell/1, the ORIGINAL source section
is the SAME ell/1. Chart separation and the original source cover prove
this identity; it is not an assumed global comparison isomorphism. -/
theorem nativeBaseSourceGlobalSection_homogeneous_fraction
    {ι : Type u} (a : ι → R) (ha : ∀ i, a i ∈ 𝒜 1)
    (hgen : Algebra.adjoin K (Set.range (fun i => algebraMap R S (a i))) = ⊤)
    (x : ∀ i, nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 (a i))
    (t : Γ(nativeProjectiveModuleSheaf 𝒜 𝒟 hR 0,⊤))
    (s : Γ(nativeProjectiveModuleSheaf 𝓑 𝒟 hS 0,⊤))
    (h : ∀ i,
      (nativeProjectiveModulePresheaf 𝒜 𝒟 hR 0).map (homOfLE le_top).op t =
        nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hR 1 (a i) (ha i) (x i) ∧
      nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS 1 (a i) (ha i) (x i) =
        (nativeProjectiveModulePresheaf 𝓑 𝒟 hS 0).map (homOfLE le_top).op s)
    (ell : 𝒟 0) (ht : t = nativeProjectiveModuleHomogeneousGlobalSection 𝒜 𝒟 hR 0 ell) :
    s = nativeProjectiveModuleHomogeneousGlobalSection 𝓑 𝒟 hS 0 ell := by
  have hcover := degreeOneGenerated_nativeProj_cover 𝓑
    (fun i => algebraMap R S (a i))
    (fun i => (normalizationBaseGradedRingHom 𝒜 𝓑).map_mem (ha i)) hgen
  have hs : ∀ i : ι,
      (nativeProjectiveModulePresheaf 𝓑 𝒟 hS 0).map
        (Proj.basicOpen 𝓑 (algebraMap R S (a i))).leTop.op s =
      (nativeProjectiveModulePresheaf 𝓑 𝒟 hS 0).map
        (Proj.basicOpen 𝓑 (algebraMap R S (a i))).leTop.op
        (nativeProjectiveModuleHomogeneousGlobalSection 𝓑 𝒟 hS 0 ell) := by
    intro i
    have hx : x i = nativeHomogeneousZeroChartElement 𝒜 𝒟 1 (a i) ell := by
      apply nativeBaseSourceBaseChartDegreeZeroSectionMap_injective 𝒜 𝓑 𝒟 hR
        1 (by decide) (a i) (ha i)
      exact (h i).1.symm.trans ((congrArg
        ((nativeProjectiveModulePresheaf 𝒜 𝒟 hR 0).map (homOfLE le_top).op) ht).trans
          (nativeHomogeneousZeroChartElement_section 𝒜 𝒟 hR 1 (a i) (ha i) ell).symm)
    exact (h i).2.symm.trans ((congrArg
      (nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS 1 (a i) (ha i)) hx).trans
        (nativeHomogeneousZeroChartElement_source_section 𝒜 𝓑 𝒟 hR hS
          1 (a i) (ha i) ell))
  apply Subtype.ext
  funext p
  have hp : p.1 ∈ ⨆ i, Proj.basicOpen 𝓑 (algebraMap R S (a i)) := by
    rw [hcover]
    trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hp
  exact congrArg (fun z => z.1 ⟨p.1,hi⟩) (hs i)
end LinearStudy
