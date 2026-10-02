module

public import Negativity.FrobeniusIntegralClosure
import Mathlib.Tactic

@[expose] public section
namespace Negativity
noncomputable section

/-- Final theorem: the integral closure of a normal finitely generated
perfect-field domain in an arbitrary finite extension of its fraction
field is finite. The separable part is proved by the trace pairing and
the purely inseparable part by the actual Frobenius scalar twist.
No separability or characteristic-zero hypothesis is imposed. -/
theorem finiteType_perfectField_normal_integralClosure_finite
    (k A K L : Type*) [Field k] [PerfectField k]
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Algebra k A] [Algebra.FiniteType k A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] : Module.Finite A (integralClosure A L) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let E := separableClosure K L
  let : Algebra A E := ((algebraMap K E).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq A K L]
    change (algebraMap K L).comp (algebraMap A K) =
      (algebraMap E L).comp ((algebraMap K E).comp (algebraMap A K))
    rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq K E L])
  have : Module.Finite A (integralClosure A E) :=
    IsIntegralClosure.finite A K E (integralClosure A E)
  obtain ⟨p, hp⟩ := ExpChar.exists k
  let : ExpChar k p := hp
  let : ExpChar A p := expChar_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective k A) p
  let : ExpChar K p := expChar_of_injective_algebraMap (IsFractionRing.injective A K) p
  let : ExpChar E p := expChar_of_injective_algebraMap (algebraMap K E).injective p
  exact finiteType_perfectField_integralClosure_purelyInseparable_finite k A E L p

end
end Negativity
