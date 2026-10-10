module
public import Linear.NormalizationHomogeneousChartProduct
public import Linear.NormalizationHomogeneousCombination
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
universe u
variable {K R S ι : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Fintype ι]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- Normalizing an actual homogeneous combination gives the expected
linear combination in the FULL original source chart. -/
theorem normalizationHomogeneousChart_combination
    (a : R) (ha : a ∈ 𝒜 1) (haB : algebraMap R S a ∈ 𝓑 1)
    (n : ℕ) (b : S) (hb : b ∈ 𝓑 n)
    (degree : ι → ℕ) (gen : ι → S) (hgen : ∀ i, gen i ∈ 𝓑 (degree i))
    (coefficient : ι → R) (hbound : ∀ i, degree i ≤ n)
    (hexpression : b = ∑ i, coefficient i • gen i) :
    HomogeneousLocalization.Away.mk 𝓑 haB n b (by simpa using hb) =
    ∑ i,
      HomogeneousLocalization.Away.mk 𝒜 ha (n-degree i)
        (gradedModuleProjection 𝒜 (n-degree i) (coefficient i))
        (by simpa [gradedModuleProjection_apply] using
          (DirectSum.decompose 𝒜 (coefficient i) (n-degree i)).property) •
      HomogeneousLocalization.Away.mk 𝓑 haB (degree i) (gen i)
        (by simpa using hgen i) := by
  classical
  have hp := normalization_homogeneous_combination 𝒜 𝓑 n b hb
    degree gen hgen coefficient hbound hexpression
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk]
  rw [hp,Localization.mk_sum]
  rw [← HomogeneousLocalization.algebraMap_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hc : gradedModuleProjection 𝒜 (n-degree i) (coefficient i) ∈ 𝒜 (n-degree i) :=
    (DirectSum.decompose 𝒜 (coefficient i) (n-degree i)).property
  have hprod := normalizationHomogeneousChart_smul_fraction 𝒜 𝓑 a ha haB
    (n-degree i) (degree i) _ hc (gen i) (hgen i)
  have hn : n-degree i+degree i = n := Nat.sub_add_cancel (hbound i)
  have hv := congrArg HomogeneousLocalization.val hprod
  rw [HomogeneousLocalization.Away.val_mk,hn] at hv
  exact hv.symm

end LinearStudy
