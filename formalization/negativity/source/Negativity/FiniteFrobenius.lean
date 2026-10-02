module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Tactic

@[expose] public section
namespace Negativity

/-- The Frobenius ring map is integral: x is a root of T^p-x^p,
whose constant coefficient comes from the actual Frobenius image. -/
theorem frobenius_isIntegral (R : Type*) [CommRing R] (p : ℕ) [ExpChar R p] :
    (frobenius R p).IsIntegral := by
  let : Algebra R R := (frobenius R p).toAlgebra
  intro x
  change IsIntegral R x
  apply IsIntegral.of_pow (expChar_pos R p)
  change IsIntegral R (algebraMap R R x)
  exact isIntegral_algebraMap

/-- Frobenius is finite on every finitely generated
algebra over a perfect field. This is the commutative-algebra ingredient
for handling the purely inseparable part of normalization finiteness.
No finiteness of Frobenius or integral closure is assumed. -/
theorem finiteType_perfectField_frobenius_finite
    (k R : Type*) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (p : ℕ) [ExpChar k p] [ExpChar R p]
    [PerfectRing k p] : (frobenius R p).Finite := by
  have hk : (frobenius k p).FiniteType :=
    RingHom.FiniteType.of_surjective _ (surjective_frobenius k p)
  have hb : (algebraMap k R).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
  have hc := hb.comp hk
  rw [RingHom.frobenius_comm] at hc
  exact (frobenius_isIntegral R p).to_finite hc.of_comp_finiteType

/-- Final theorem: every iterated Frobenius is finite on a finitely
generated perfect-field algebra. This supplies the actual finite scalar
restriction needed for a finite purely inseparable normalization step. -/
theorem finiteType_perfectField_iterateFrobenius_finite
    (k R : Type*) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (p : ℕ) [ExpChar k p] [ExpChar R p]
    [PerfectRing k p] (n : ℕ) : (iterateFrobenius R p n).Finite := by
  induction n with
  | zero => simpa only [iterateFrobenius_zero] using RingHom.Finite.id R
  | succ n ih =>
    rw [iterateFrobenius_add, iterateFrobenius_one]
    exact ih.comp (finiteType_perfectField_frobenius_finite k R p)

end Negativity
