module

public import Negativity.AffineCurveOrders
public import Negativity.FiniteNormalGeometry
public import Negativity.CurveDegree
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory IsDedekindDomain
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (U : Y.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]

local instance : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
theorem finite_curve_chart_generic_tower :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    letI : Algebra Γ(Y, U) X.functionField :=
      ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom).toAlgebra
    IsScalarTower Γ(Y, U) Y.functionField X.functionField := by
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  let : Algebra Γ(Y, U) X.functionField :=
    ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (dominantFunctionFieldMap_germ f U r).symm

theorem dominant_curve_chart_torsionFree :
    Module.IsTorsionFree Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  intro r s hrs
  apply Y.germToFunctionField_injective U
  apply (dominantFunctionFieldMap f).injective
  rw [dominantFunctionFieldMap_germ f U, dominantFunctionFieldMap_germ f U]
  exact congrArg (X.germToFunctionField (f ⁻¹ᵁ U)) hrs

/-- Final theorem: for an actual finite dominant map of normal curves,
the local order formula summed over the actual coordinate-ring primes of
each geometric fiber equals function-field degree times the target order.
The coordinate maps, generic maps, field towers, torsion-freeness and
flatness are derived from the actual Scheme morphism. No separability or
chosen ramification weights are assumed. Global divisor summation is the
next separate step. -/
theorem finite_normal_curve_fiber_order_degree
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsFinite f]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdX : Order.krullDim X ≤ 1) (hdY : Order.krullDim Y ≤ 1)
    (hU : IsAffineOpen U) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    letI : Algebra Γ(Y, U) X.functionField :=
      ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom).toAlgebra
    letI := normal_curve_affine_dedekind Y hnY hdY U hU
    letI := normal_curve_affine_dedekind X hnX hdX (f ⁻¹ᵁ U) (hU.preimage f)
    letI := dominant_curve_chart_torsionFree f U
    letI : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
    ∀ (p : HeightOneSpectrum Γ(Y, U)) (a : Y.functionFieldˣ),
      letI : Fintype (p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U)) :=
        Fintype.ofFinite (p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U))
      ∑ q : p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U),
        schemeRationalOrder X hnX ((hU.preimage f).fromSpec
          ⟨q.1, inferInstance⟩)
          (curve_affine_prime_coheight X (f ⁻¹ᵁ U) (hU.preimage f)
            (heightOnePrimeAbove p q))
          (Units.map (dominantFunctionFieldMap f).toMonoidHom a) * (q.1.inertiaDeg Γ(Y, U) : ℤ) =
        schemeRationalOrder Y hnY (hU.fromSpec ⟨p.asIdeal, inferInstance⟩)
          (curve_affine_prime_coheight Y U hU p) a *
          (Module.finrank Y.functionField X.functionField : ℤ) := by
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  let : Algebra Γ(Y, U) X.functionField :=
    ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom).toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := normal_curve_affine_dedekind Y hnY hdY U hU
  have := normal_curve_affine_dedekind X hnX hdX (f ⁻¹ᵁ U) (hU.preimage f)
  have := dominant_curve_chart_torsionFree f U
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  have := finite_curve_chart_generic_tower f U
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have := functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ U) (hU.preimage f)
  have : Module.Flat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := inferInstance
  intro p a
  let : Fintype (p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U)) := Fintype.ofFinite _
  have he := finite_flat_order_fiber_degree (R := Γ(Y, U)) (S := Γ(X, f ⁻¹ᵁ U))
    (K := Y.functionField) X.functionField p a
  simp only [normal_curve_affine_prime_order X hnX (f ⁻¹ᵁ U) (hU.preimage f),
    normal_curve_affine_prime_order Y hnY U hU, heightOnePrimeAbove,
    RingHom.algebraMap_toAlgebra] at he
  convert he using 1

end
end Negativity
