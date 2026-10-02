module

public import Negativity.InfinityNorm
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open IsDedekindDomain Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FunctionFieldPlaces
variable (k L : Type*) [Field k] [Field L] [Algebra (RatFunc k) L]
local notation3 "K" => RatFunc k
local notation3 "R" => k[X]
local notation3 "A" => RationalInfinityRing k

local instance (priority := low) : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
local instance : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
local instance : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr <|
  (algebraMap K L).injective.comp (IsFractionRing.injective R K)
local instance (priority := low) : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
local instance : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
local instance : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr <|
  (algebraMap K L).injective.comp (IsFractionRing.injective A K)

/-- Normalization of the actual affine t-line in the curve function field. -/
def FiniteRing := integralClosure R L
local notation3 "S" => FiniteRing k L
instance : CommRing S := inferInstanceAs (CommRing (integralClosure R L))
instance : IsDomain S := inferInstanceAs (IsDomain (integralClosure R L))
instance : Algebra R S := inferInstanceAs (Algebra R (integralClosure R L))
instance : Algebra S L := inferInstanceAs (Algebra (integralClosure R L) L)
instance : IsScalarTower R S L := inferInstanceAs (IsScalarTower R (integralClosure R L) L)
instance : IsIntegralClosure S R L :=
  inferInstanceAs (IsIntegralClosure (integralClosure R L) R L)
instance : Module.IsTorsionFree R S := Subalgebra.instIsTorsionFree (integralClosure R L)
instance : Algebra k S := ((algebraMap R S).comp (algebraMap k R)).toAlgebra
instance : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq' rfl

/-- Integral closure of the actual infinity DVR in the same function field. -/
def InfinityRing := integralClosure A L
local notation3 "B" => InfinityRing k L
instance : CommRing B := inferInstanceAs (CommRing (integralClosure A L))
instance : IsDomain B := inferInstanceAs (IsDomain (integralClosure A L))
instance : Algebra A B := inferInstanceAs (Algebra A (integralClosure A L))
instance : Algebra B L := inferInstanceAs (Algebra (integralClosure A L) L)
instance : IsScalarTower A B L := inferInstanceAs (IsScalarTower A (integralClosure A L) L)
instance : IsIntegralClosure B A L :=
  inferInstanceAs (IsIntegralClosure (integralClosure A L) A L)
instance : Module.IsTorsionFree A B := Subalgebra.instIsTorsionFree (integralClosure A L)

variable [FiniteDimensional (RatFunc k) L] [Algebra.IsSeparable (RatFunc k) L]
instance : Module.Finite R S := IsIntegralClosure.finite R K L S
instance : IsDedekindDomain S := integralClosure.isDedekindDomain R K L
instance : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
instance : Algebra.FiniteType k S := Algebra.FiniteType.trans
  (inferInstance : Algebra.FiniteType k k[X]) (inferInstance : Algebra.FiniteType k[X] S)
instance : Module.Finite A B := IsIntegralClosure.finite A K L B
instance : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
instance : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L

/-- Total divisor degree, using actual finite places and actual local
places over infinity. The infinity weights are residue degrees over the
infinity residue field; identifying that residue field with k and these
places with a supplied complete Scheme curve remains a geometric bridge. -/
def principalDegree (a : Lˣ) : ℤ :=
  affineDivisorDegree k S (affinePrincipalDivisor L a) +
    (affineDivisorPushforward A B (affinePrincipalDivisor L a))
      (IsDiscreteValuationRing.maximalIdeal A)

/-- The norm/valuation product formula for finite separable extensions of
k(t), in arbitrary characteristic. The normalization rings are constructed;
no finite-chart existence, divisor identity or degree-zero premise is assumed. -/
theorem principalDegree_eq_zero (a : Lˣ) : principalDegree k L a = 0 := by
  exact twoChart_principal_degree_zero k S B L a

end FunctionFieldPlaces
end

/-- The function-field product formula with constructed normal rings at
finite places and infinity. This is an algebraic auxiliary to geometric
line-bundle degree, not the final geometric negativity lemma. -/
theorem functionField_principal_degree_zero (k L : Type*) [Field k] [Field L]
    [Algebra (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    [Algebra.IsSeparable (RatFunc k) L] (a : Lˣ) :
    FunctionFieldPlaces.principalDegree k L a = 0 :=
  FunctionFieldPlaces.principalDegree_eq_zero k L a

end Negativity
