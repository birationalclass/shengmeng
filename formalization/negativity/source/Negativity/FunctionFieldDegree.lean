module

public import Negativity.FunctionFieldProductFormula
public import Negativity.RationalInfinityResidue
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FunctionFieldPlaces
variable (k L : Type*) [Field k] [Field L] [Algebra (RatFunc k) L]

noncomputable instance infinityBaseAlgebra : Algebra k (InfinityRing k L) :=
  ((algebraMap (RationalInfinityRing k) (InfinityRing k L)).comp
    (rationalInfinityConstantHom k)).toAlgebra

instance infinityBaseTower : IsScalarTower k (RationalInfinityRing k) (InfinityRing k L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Actual residue-weighted order sum at every constructed place, with
both finite and infinity weights measured over the same field k. -/
noncomputable def baseFieldPrincipalDegree
    [FiniteDimensional (RatFunc k) L] [Algebra.IsSeparable (RatFunc k) L] (a : Lˣ) : ℤ :=
  affineDivisorDegree k (FiniteRing k L) (affinePrincipalDivisor L a) +
    affineDivisorDegree k (InfinityRing k L) (affinePrincipalDivisor L a)

end FunctionFieldPlaces

/-- Product formula with genuine k-residue weights, including infinity.
No residue-weight compatibility premise is used. The rings are constructed
as integral closures; identifying their places with a supplied complete
Scheme curve remains to be proved separately. -/
theorem functionField_principal_degree_baseField_zero (k L : Type*) [Field k] [Field L]
    [Algebra (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    [Algebra.IsSeparable (RatFunc k) L] (a : Lˣ) :
    FunctionFieldPlaces.baseFieldPrincipalDegree k L a = 0 := by
  unfold FunctionFieldPlaces.baseFieldPrincipalDegree
  rw [infinity_pushforward_degree k (FunctionFieldPlaces.InfinityRing k L)
    (affinePrincipalDivisor L a)]
  exact functionField_principal_degree_zero k L a

/-- Over an algebraically closed field, all actual residue weights are one,
so the norm/valuation product formula is the direct sum of local orders.
Arbitrary characteristic is permitted. Identifying these constructed places
with a supplied complete curve is the remaining geometric bridge. -/
theorem functionField_principal_order_sum_zero (k L : Type*) [Field k] [IsAlgClosed k]
    [Field L] [Algebra (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    [Algebra.IsSeparable (RatFunc k) L] (a : Lˣ) :
    (affinePrincipalDivisor L a :
      IsDedekindDomain.HeightOneSpectrum (FunctionFieldPlaces.FiniteRing k L) →₀ ℤ).degree +
    (affinePrincipalDivisor L a :
      IsDedekindDomain.HeightOneSpectrum (FunctionFieldPlaces.InfinityRing k L) →₀ ℤ).degree = 0 := by
  have h := functionField_principal_degree_baseField_zero k L a
  unfold FunctionFieldPlaces.baseFieldPrincipalDegree at h
  rw [affineDivisorDegree_eq_order_sum k (FunctionFieldPlaces.FiniteRing k L)
      (closedPoint_residueDegree_one k (FunctionFieldPlaces.FiniteRing k L)),
    affineDivisorDegree_eq_order_sum k (FunctionFieldPlaces.InfinityRing k L)
      (algebraicallyClosed_infinity_point_degree_one k (FunctionFieldPlaces.InfinityRing k L))] at h
  exact h

end Negativity
