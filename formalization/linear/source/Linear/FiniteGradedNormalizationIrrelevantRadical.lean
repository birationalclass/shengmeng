module
public import Linear.NormalizationHomogeneousCombination
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]

/-- Finiteness of the actual graded normalization makes the irrelevant
ideal of the source lie in the radical of the extended base irrelevant
ideal. The stronger ideal containment required by mathlib's Proj.map
is not assumed. This is the no-base-locus input for the original map. -/
theorem finiteGradedNormalization_irrelevant_le_radical :
    (HomogeneousIdeal.irrelevant 𝓑).toIdeal ≤
      (Ideal.map (algebraMap R S) (HomogeneousIdeal.irrelevant 𝒜).toIdeal).radical := by
  classical
  obtain ⟨s,hs,hpieces⟩ := finiteModule_exists_homogeneous_generators (A := R) 𝓑
  let degree : s → ℕ := fun i => (hpieces i.val i.property).choose
  let gen : s → S := Subtype.val
  have hgen (i : s) : gen i ∈ 𝓑 (degree i) := (hpieces i.val i.property).choose_spec
  have hrange : Set.range gen = (s : Set S) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩; exact i.property
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
  let m := Finset.univ.sup degree
  have hbound (i : s) : degree i ≤ m := Finset.le_sup (Finset.mem_univ i)
  apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝓑).mpr
  intro j hj b hb
  change b ∈ 𝓑 j at hb
  let N := j*(m+1)
  have hmN : m < N := by dsimp [N]; nlinarith
  have hbN : b^(m+1) ∈ 𝓑 N := by
    simpa only [N,smul_eq_mul,mul_comm] using SetLike.pow_mem_graded (m+1) hb
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp
    (show b^(m+1) ∈ Submodule.span R (Set.range gen) by rw [hrange,hs]; trivial)
  have hex := normalization_homogeneous_combination 𝒜 𝓑 N (b^(m+1)) hbN
    degree gen hgen c (fun i => (hbound i).trans hmN.le) hc.symm
  refine Ideal.mem_radical_iff.mpr ⟨m+1,?_⟩
  rw [hex]
  apply Ideal.sum_mem
  intro i hi
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_right
  apply Ideal.mem_map_of_mem
  have hiN : degree i < N := (hbound i).trans_lt hmN
  apply HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 (show 0 < N-degree i by omega)
  exact (DirectSum.decompose 𝒜 (c i) (N-degree i)).property

end LinearStudy
