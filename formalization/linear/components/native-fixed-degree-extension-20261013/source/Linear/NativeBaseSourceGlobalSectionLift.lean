module
public import Linear.NativeBaseSourceChartOverlapGluing
public import Linear.SchemeModuleHomActualSectionGluing
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K S M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] [SetLike.GradedSMul 𝒜 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable [IsDomain S] [Module.IsTorsionFree S M]
variable [IsNoetherianRing S] [Module.Finite S M]
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- Every actual source global section comes from actual base global
sections on a degree-one base cover. The local fraction comparison,
surjectivity, overlap equality and sheaf gluing are proved, not assumed.
The equality is recorded on each ORIGINAL chart using the SAME fractions. -/
theorem nativeBaseSourceGlobalSection_exists_lift
    {ι : Type u} (a : ι → R) (ha : ∀ i, a i ∈ 𝒜 1)
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ i, Proj.basicOpen 𝒜 (a i))
    (hgen : Algebra.adjoin K (Set.range (fun i => algebraMap R S (a i))) = ⊤)
    (s : Γ(nativeProjectiveModuleSheaf 𝓑 𝒟 hS 0,⊤)) :
    ∃ x : ∀ i, nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 (a i),
    ∃ t : Γ(nativeProjectiveModuleSheaf 𝒜 𝒟 hR 0,⊤), ∀ i,
      (nativeProjectiveModulePresheaf 𝒜 𝒟 hR 0).map (homOfLE le_top).op t =
        nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hR 1 (a i) (ha i) (x i) ∧
      nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS 1 (a i) (ha i) (x i) =
        (nativeProjectiveModulePresheaf 𝓑 𝒟 hS 0).map (homOfLE le_top).op s := by
  classical
  let U := fun i => Proj.basicOpen 𝒜 (a i)
  let US := fun i => Proj.basicOpen 𝓑 (algebraMap R S (a i))
  let A := nativeProjectiveModuleSheaf 𝒜 𝒟 hR 0
  let B := nativeProjectiveModuleSheaf 𝓑 𝒟 hS 0
  have hx : ∀ i, ∃ x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 (a i),
      nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS 1 (a i) (ha i) x =
        B.presheaf.map (US i).leTop.op s := by
    intro i
    exact (nativeBaseSourceWeightedChartSection_bijective 𝒜 𝓑 𝒟 hR hS
      (fun j => algebraMap R S (a j))
      (fun j => (normalizationBaseGradedRingHom 𝒜 𝓑).map_mem (ha j)) hgen
      (a i) (ha i)).surjective _
  choose x hx using hx
  let sigma := fun i => nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hR
    1 (a i) (ha i) (x i)
  have hc : TopCat.Presheaf.IsCompatible A.presheaf U sigma := by
    intro i j
    exact schemeModuleSections_infRestrictionEq_of_originalEqualOpen A
      (U i) (U j) (Proj.basicOpen 𝒜 (a i*a j))
      (ProjectiveSpectrum.basicOpen_mul 𝒜 (a i) (a j))
      (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 (a i) (a j))
      (ProjectiveSpectrum.basicOpen_mul_le_right 𝒜 (a i) (a j)) (sigma i) (sigma j)
      (nativeBaseSourceChartSection_overlap_agrees 𝒜 𝓑 𝒟 hR hS
        (a i) (a j) (ha i) (ha j) (x i) (x j) s (hx i) (hx j))
  let F : TopCat.Sheaf AddCommGrpCat.{u} (Proj 𝒜) := ⟨A.presheaf,A.isSheaf⟩
  obtain ⟨t,ht,-⟩ := F.existsUnique_gluing' U ⊤ (fun i => (U i).leTop) hcover sigma hc
  exact ⟨x,t,fun i => ⟨ht i,hx i⟩⟩
end LinearStudy
