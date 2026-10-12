module
public import Linear.NormalizationHomogeneousChartSum
public import Linear.NormalizationHomogeneousChartShift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
universe u
variable {K R S ι : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Fintype ι]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- Actual homogeneous source-module generators generate the FULL source
chart after dividing each one by its corresponding ORIGINAL denominator
power. The common degree bound is only used to prove generation. -/
theorem normalizationHomogeneousChart_span
    (a : R) (ha : a ∈ 𝒜 1) (haB : algebraMap R S a ∈ 𝓑 1)
    (degree : ι → ℕ) (gen : ι → S) (hgen : ∀ i, gen i ∈ 𝓑 (degree i))
    (hspan : Submodule.span R (Set.range gen) = ⊤)
    (m : ℕ) (hbound : ∀ i, degree i ≤ m) :
    Submodule.span (HomogeneousLocalization.Away 𝒜 a)
      (Set.range fun i => HomogeneousLocalization.Away.mk 𝓑 haB
        (degree i) (gen i) (by simpa using hgen i)) = ⊤ := by
  classical
  apply top_unique
  intro z hz
  obtain ⟨n,b,hb,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝓑 haB z
  have hb' : b ∈ 𝓑 n := by simpa using hb
  let b' := (algebraMap R S a)^m * b
  have hbg : b' ∈ 𝓑 (n+m) := by
    simpa [b',add_comm] using
      SetLike.mul_mem_graded (SetLike.pow_mem_graded m haB) hb'
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp
    (show b' ∈ Submodule.span R (Set.range gen) by rw [hspan]; trivial)
  have hc' := normalizationHomogeneousChart_combination 𝒜 𝓑 a ha haB
    (n+m) b' hbg degree gen hgen c (fun i => (hbound i).trans (Nat.le_add_left _ _)) hc.symm
  have hs := normalizationHomogeneousChart_shift_fraction (𝓑 := 𝓑) a haB n m b hb'
  rw [← hs,hc']
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

end LinearStudy
