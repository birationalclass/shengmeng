module

public import Negativity.FiniteCurveOrders
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors
universe u
set_option backward.isDefEq.respectTransparency false

/-- Final theorem: an actual finite dominant map of integral schemes
induces a finite extension of their actual function fields. Neither
normality nor separability nor dimension one is an input. -/
theorem finite_dominant_functionField_finite
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) [IsFinite f] [IsDominant f] :
    letI : Algebra X.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
    FiniteDimensional X.functionField C.functionField := by
  let : Algebra X.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
  obtain ⟨U, hU, hη, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint X) trivial
  have : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
  have hηC : f (genericPoint C) ∈ U := by rw [dominant_genericPoint_eq f]; exact hη
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨genericPoint C, hηC⟩⟩
  let A := Γ(X, U)
  let B := Γ(C, f ⁻¹ᵁ U)
  let : Algebra A B := (f.app U).hom.toAlgebra
  let : Algebra A C.functionField :=
    ((C.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom).toAlgebra
  have : IsScalarTower A B C.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := finite_curve_chart_generic_tower f U
  have : Module.Finite A B := f.finite_app U hU
  have := dominant_curve_chart_torsionFree f U
  have : Algebra.IsIntegral A B := ⟨IsIntegral.of_finite A⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have := functionField_isFractionRing_of_isAffineOpen C (f ⁻¹ᵁ U) (hU.preimage f)
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) C.functionField := inferInstance
  exact Module.Finite.of_isLocalization A B A⁰

end Negativity
