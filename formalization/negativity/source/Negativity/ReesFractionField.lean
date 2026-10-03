module

public import Negativity.FiniteNormalizationAlgebra
public import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

abbrev reesPolynomialFractionAlgebra (I : Ideal R) :
    Algebra (reesAlgebra I) (FractionRing R[X]) :=
  inferInstance

theorem polynomial_scaled_mem_rees
    (I : Ideal R) {a : R} (ha : a ∈ I) (p : R[X]) (n : ℕ)
    (hn : p.natDegree ≤ n) : C (a ^ n) * p ∈ reesAlgebra I := by
  intro i
  rw [coeff_C_mul]
  by_cases hi : i ≤ p.natDegree
  · exact Ideal.mul_mem_right _ _
      ((Ideal.pow_le_pow_right (hi.trans hn)) (Ideal.pow_mem_pow ha n))
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi), mul_zero]
    exact Ideal.zero_mem _

/-- Final theorem: for every nonzero ideal in a domain, its Rees algebra
has the same fraction field as the full polynomial ring. Denominators
are constructed by multiplying each polynomial by a sufficiently high
power of a fixed nonzero ideal element. -/
theorem rees_algebra_polynomial_fraction_field (I : Ideal R) (hI : I ≠ ⊥) :
    letI := reesPolynomialFractionAlgebra I
    IsFractionRing (reesAlgebra I) (FractionRing R[X]) := by
  let : Algebra (reesAlgebra I) (FractionRing R[X]) := reesPolynomialFractionAlgebra I
  have hinj : Function.Injective (algebraMap (reesAlgebra I) (FractionRing R[X])) :=
    (IsFractionRing.injective R[X] (FractionRing R[X])).comp Subtype.val_injective
  have : FaithfulSMul (reesAlgebra I) (FractionRing R[X]) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  apply IsFractionRing.of_field
  intro z
  obtain ⟨p, q, _hq, rfl⟩ := IsFractionRing.div_surjective R[X] z
  let n := max p.natDegree q.natDegree
  let c := C (a ^ n)
  have hc : c ≠ 0 := by simp [c, ha0]
  refine ⟨⟨c * p, polynomial_scaled_mem_rees I ha p n (le_max_left _ _)⟩,
    ⟨c * q, polynomial_scaled_mem_rees I ha q n (le_max_right _ _)⟩, ?_⟩
  change algebraMap R[X] (FractionRing R[X]) p /
      algebraMap R[X] (FractionRing R[X]) q =
    algebraMap R[X] (FractionRing R[X]) (c * p) /
      algebraMap R[X] (FractionRing R[X]) (c * q)
  simp only [map_mul]
  rw [mul_div_mul_left _ _ ((map_ne_zero_iff _
    (IsFractionRing.injective R[X] (FractionRing R[X]))).mpr hc)]

end
end Negativity
