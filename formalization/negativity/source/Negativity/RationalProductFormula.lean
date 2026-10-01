module

public import Mathlib.FieldTheory.RatFunc.Valuation
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open Polynomial UniqueFactorizationMonoid

/-- Irreducible factors are counted with their actual multiplicities, and
weighted by their polynomial degrees. No degree identity is assumed. -/
theorem polynomial_factor_degree_sum {F : Type*} [Field F] [DecidableEq F]
    (p : F[X]) (hp : p ≠ 0) :
    ((normalizedFactors p).map Polynomial.natDegree).sum = p.natDegree := by
  rw [← Polynomial.natDegree_multiset_prod _ (zero_notMem_normalizedFactors p),
    prod_normalizedFactors_eq hp, Polynomial.natDegree_normalize]

/-- The order at infinity supplied by the actual valuation on F(t). -/
noncomputable def rationalInfinityOrder {F : Type*} [Field F] (a : RatFunc F) : ℤ := by
  classical
  exact -WithZero.log (RatFunc.inftyValuation F a)

theorem rationalInfinityOrder_eq {F : Type*} [Field F]
    (a : RatFunc F) (ha : a ≠ 0) :
    rationalInfinityOrder a = -a.intDegree := by
  classical
  simp [rationalInfinityOrder, RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero F ha]

/-- The product formula on the rational function field: the finite-place
contribution is written as the multiset of irreducible numerator and
denominator factors, with multiplicity and residue-degree weights deg(p).
This proves the base F(t) calculation, not yet the norm transport to a
general complete curve or a definition of degree for line bundles. -/
theorem rationalFunction_principal_degree_zero {F : Type*} [Field F] [DecidableEq F]
    (a : RatFunc F) (ha : a ≠ 0) :
    (((normalizedFactors a.num).map Polynomial.natDegree).sum : ℤ) -
      (((normalizedFactors a.denom).map Polynomial.natDegree).sum : ℤ) +
      rationalInfinityOrder a = 0 := by
  rw [polynomial_factor_degree_sum a.num (RatFunc.num_ne_zero ha),
    polynomial_factor_degree_sum a.denom a.denom_ne_zero,
    rationalInfinityOrder_eq a ha]
  simp [RatFunc.intDegree]

end Negativity
