module

public import Negativity.CurveClosedResidue
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory IsDedekindDomain
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (hU : IsAffineOpen U) (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdX : Order.krullDim X ≤ 1) (hdY : Order.krullDim Y ≤ 1)

local instance : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra

include k b hU hnX hnY hdX hdY in
/-- The local degree sum with every residue-field weight proved equal to one. -/
theorem finite_normal_curve_unweighted_order_degree :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    letI := normal_curve_affine_dedekind Y hnY hdY U hU
    letI := normal_curve_affine_dedekind X hnX hdX (f ⁻¹ᵁ U) (hU.preimage f)
    letI := dominant_curve_chart_torsionFree f U
    letI : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
    ∀ (p : HeightOneSpectrum Γ(Y, U)) (a : Y.functionFieldˣ),
      letI : Fintype (p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U)) := Fintype.ofFinite _
      ∑ q : p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U),
        schemeRationalOrder X hnX ((hU.preimage f).fromSpec ⟨q.1, inferInstance⟩)
          (curve_affine_prime_coheight X (f ⁻¹ᵁ U) (hU.preimage f)
            (heightOnePrimeAbove p q))
          (Units.map (dominantFunctionFieldMap f).toMonoidHom a) =
        schemeRationalOrder Y hnY (hU.fromSpec ⟨p.asIdeal, inferInstance⟩)
          (curve_affine_prime_coheight Y U hU p) a *
          (Module.finrank Y.functionField X.functionField : ℤ) := by
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  have := normal_curve_affine_dedekind Y hnY hdY U hU
  have := normal_curve_affine_dedekind X hnX hdX (f ⁻¹ᵁ U) (hU.preimage f)
  have := dominant_curve_chart_torsionFree f U
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  intro p a
  let : Fintype (p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U)) := Fintype.ofFinite _
  have he := finite_normal_curve_fiber_order_degree f U hnX hnY hdX hdY hU p a
  have hq := finite_normal_curve_relative_residueDegree_one f U hU k b hnX hnY hdX hdY p
  simpa only [hq, Int.natCast_one, mul_one] using he

include k b hU hnX hnY hdX hdY in
/-- Final theorem: sum actual local orders over every actual point of a
Scheme fiber. The fiber-to-prime correspondence is constructed, the
closed-point condition is derived, and the result is the full function-field
degree times the target order. This includes inseparable finite morphisms. -/
theorem finite_normal_curve_actual_fiber_order_degree :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    letI := normal_curve_affine_dedekind Y hnY hdY U hU
    letI := normal_curve_affine_dedekind X hnX hdX (f ⁻¹ᵁ U) (hU.preimage f)
    letI := dominant_curve_chart_torsionFree f U
    letI : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
    ∀ (p : HeightOneSpectrum Γ(Y, U)) (a : Y.functionFieldˣ),
      letI : Fintype (p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U)) := Fintype.ofFinite _
      letI : Fintype {x : X // f x = hU.fromSpec ⟨p.asIdeal, inferInstance⟩} :=
        Fintype.ofEquiv _ (curveFiberPrimeEquiv f U hU ⟨p.asIdeal, inferInstance⟩)
      ∑ x : {x : X // f x = hU.fromSpec ⟨p.asIdeal, inferInstance⟩},
        (if hx : Order.coheight (x : X) = 1 then
          schemeRationalOrder X hnX x hx (Units.map (dominantFunctionFieldMap f).toMonoidHom a)
        else 0) =
        schemeRationalOrder Y hnY (hU.fromSpec ⟨p.asIdeal, inferInstance⟩)
          (curve_affine_prime_coheight Y U hU p) a *
          (Module.finrank Y.functionField X.functionField : ℤ) := by
  classical
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  have := normal_curve_affine_dedekind Y hnY hdY U hU
  have := normal_curve_affine_dedekind X hnX hdX (f ⁻¹ᵁ U) (hU.preimage f)
  have := dominant_curve_chart_torsionFree f U
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  intro p a
  let : Fintype (p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U)) := Fintype.ofFinite _
  let e := curveFiberPrimeEquiv f U hU ⟨p.asIdeal, inferInstance⟩
  let : Fintype {x : X // f x = hU.fromSpec ⟨p.asIdeal, inferInstance⟩} := Fintype.ofEquiv _ e
  rw [← e.sum_comp]
  have he := finite_normal_curve_unweighted_order_degree f U hU k b hnX hnY hdX hdY p a
  convert he using 1
  apply Finset.sum_congr rfl
  intro q _
  have hx := curve_affine_prime_coheight X (f ⁻¹ᵁ U) (hU.preimage f) (heightOnePrimeAbove p q)
  change Order.coheight ((hU.preimage f).fromSpec ⟨q.1, inferInstance⟩) = 1 at hx
  change (if hx : Order.coheight ((hU.preimage f).fromSpec ⟨q.1, inferInstance⟩) = 1 then
    schemeRationalOrder X hnX _ hx _ else 0) = _
  exact dite_eq_left hx

end
end Negativity
