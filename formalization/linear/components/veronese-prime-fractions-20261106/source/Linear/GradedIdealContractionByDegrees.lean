module
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
variable {L R T : Type*} [Field L] [CommRing R] [CommRing T]
variable [Algebra L R] [Algebra L T]
variable (A : ℕ → Submodule L R) [GradedAlgebra A]
variable (A' : ℕ → Submodule L T) [GradedAlgebra A']
variable (j : R →+* T) (g : ℕ → ℕ) (hg : Function.Injective g)
variable (hj : ∀ n : ℕ, ∀ z ∈ A n, j z ∈ A' (g n))
include hg hj

/-- A map with an injective change of degree commutes with the corresponding
original homogeneous projections. -/
theorem gradedRing_proj_map_injectiveDegrees (n : ℕ) (z : R) :
    j (GradedRing.proj A n z) = GradedRing.proj A' (g n) (j z) := by
  induction z using DirectSum.Decomposition.inductionOn A with
  | zero => simp only [map_zero]
  | @homogeneous m z =>
    simp only [GradedRing.proj_apply]
    by_cases hm : m = n
    · subst m
      rw [DirectSum.decompose_of_mem_same A z.property,
        DirectSum.decompose_of_mem_same A' (hj n z z.property)]
    · rw [DirectSum.decompose_of_mem_ne A z.property hm,
        DirectSum.decompose_of_mem_ne A' (hj m z z.property) (fun h => hm (hg h)),
        map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Comparison on homogeneous elements determines contraction of the whole
ideal when the ambient degrees of the source pieces are distinct. -/
theorem homogeneousIdeal_toIdeal_eq_comap_of_compare
    (I : HomogeneousIdeal A) (J : HomogeneousIdeal A')
    (h : ∀ n : ℕ, ∀ z ∈ A n, z ∈ I.toIdeal ↔ j z ∈ J.toIdeal) :
    I.toIdeal = J.toIdeal.comap j := by
  classical
  ext z
  change z ∈ I.toIdeal ↔ j z ∈ J.toIdeal
  constructor
  · intro hz
    have hc := (I.isHomogeneous.mem_iff.mp hz)
    rw [← DirectSum.sum_support_decompose A z, map_sum]
    exact Ideal.sum_mem _ (fun n _ => (h n _ (DirectSum.decompose A z n).property).mp (hc n))
  · intro hz
    apply I.isHomogeneous.mem_iff.mpr
    intro n
    apply (h n _ (DirectSum.decompose A z n).property).mpr
    have hc := (J.isHomogeneous.mem_iff.mp hz) (g n)
    exact (gradedRing_proj_map_injectiveDegrees A A' j g hg hj n z).symm ▸ hc

end LinearStudy
#check LinearStudy.gradedRing_proj_map_injectiveDegrees
#print axioms LinearStudy.gradedRing_proj_map_injectiveDegrees
#check LinearStudy.homogeneousIdeal_toIdeal_eq_comap_of_compare
#print axioms LinearStudy.homogeneousIdeal_toIdeal_eq_comap_of_compare

