module

public import Negativity.FiniteNormalizationAlgebra
import Mathlib.Tactic

@[expose] public section
namespace Negativity
noncomputable section

/-- Final theorem: an actual intermediate algebra inside a finite
function-field extension has finite relative integral closure. The
embedding is used to inject its closure into the proved finite closure
in the field; no finiteness of the intermediate algebra is needed. -/
theorem finiteType_perfectField_relative_integralClosure_finite
    (k A K L S : Type*) [Field k] [PerfectField k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [CommRing S] [Algebra A S]
    (j : S →ₐ[A] L) (hj : Function.Injective j) :
    Module.Finite A (integralClosure A S) := by
  have : Module.Finite A (integralClosure A L) :=
    finiteType_perfectField_integralClosure_finite k A K L
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let h : integralClosure A S →ₐ[A] integralClosure A L := {
    toFun x := ⟨j x, x.property.map j⟩
    map_zero' := Subtype.ext (map_zero j)
    map_one' := Subtype.ext (map_one j)
    map_add' x y := Subtype.ext (map_add j (x : S) (y : S))
    map_mul' x y := Subtype.ext (map_mul j (x : S) (y : S))
    commutes' a := Subtype.ext (j.commutes a) }
  apply Module.Finite.of_injective h.toLinearMap
  intro x y hxy
  apply Subtype.ext
  exact hj (congrArg Subtype.val hxy)

end
end Negativity
