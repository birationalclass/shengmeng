module

public import Negativity.FiniteCurvePoints
public import Negativity.CartierDegree
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
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdX : Order.krullDim X ≤ 1) (hdY : Order.krullDim Y ≤ 1)

local instance (y : Y) : Fintype {x : X // f x = y} := by
  change Fintype (f ⁻¹' {y})
  exact (f.finite_preimage_singleton y).fintype

include k b hdX hdY

/-- Final theorem: construct the actual Cartier pullback and prove its
coefficient sum over each actual closed-point fiber equals the target
Cartier coefficient times the function-field degree. All orders and fiber
maps come from actual Scheme geometry, not an assumed projection formula. -/
theorem finite_normal_curve_cartier_fiber_orders {ι : Type*} (A : CartierAtlas Y ι) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    ∃ B : CartierAtlas X X,
      (∀ z : X, B.chart z ≤ f ⁻¹ᵁ A.chart (A.covers (f z)).choose ∧ z ∈ B.chart z ∧
        B.equation z = Units.map (dominantFunctionFieldMap f).toMonoidHom
          (A.equation (A.covers (f z)).choose)) ∧
      ∀ (y : Y), Order.coheight y = 1 →
      ∑ x : {x : X // f x = y}, B.coefficient hnX x =
        A.coefficient hnY y * (Module.finrank Y.functionField X.functionField : ℤ) := by
  classical
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  obtain ⟨B, hB⟩ := exists_cartierAtlas_pullback f A
  refine ⟨B, hB, ?_⟩
  intro y hy
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  have := finite_dominant_curve_preimage_nonempty f U
  let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have := normal_curve_affine_dedekind Y hnY hdY U hU
  have := normal_curve_affine_dedekind X hnX hdX (f ⁻¹ᵁ U) (hU.preimage f)
  have := dominant_curve_chart_torsionFree f U
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  obtain ⟨p, hp⟩ := curve_affine_point_heightOne Y U hU y hyU hy
  subst y
  let y : Y := hU.fromSpec ⟨p.asIdeal, inferInstance⟩
  have he := finite_normal_curve_actual_fiber_order_degree f U hU k b hnX hnY hdX hdY p
    (A.equation (A.covers y).choose)
  rw [← cartierAtlas_coefficient_eq Y hnY A _ y hy (A.covers y).choose_spec] at he
  convert he using 1
  apply Finset.sum_congr (by ext x; simp)
  intro x _
  have hx : Order.coheight (x : X) = 1 := by
    obtain ⟨q, hq⟩ := (curveFiberPrimeEquiv f U hU ⟨p.asIdeal, inferInstance⟩).surjective
      ⟨x, x.2⟩
    have hxc := curve_affine_prime_coheight X (f ⁻¹ᵁ U) (hU.preimage f) (heightOnePrimeAbove p q)
    change Order.coheight ((hU.preimage f).fromSpec ⟨q.1, inferInstance⟩) = 1 at hxc
    have hxe := congrArg Subtype.val hq
    change (hU.preimage f).fromSpec ⟨q.1, inferInstance⟩ = x at hxe
    simpa only [hxe] using hxc
  rw [dite_eq_left hx, cartierAtlas_coefficient_eq X hnX B x x hx (hB x).2.1,
    (hB x).2.2]
  congr 2
  exact congrArg (fun t : Y => A.equation (A.covers t).choose) x.2

end
end Negativity
