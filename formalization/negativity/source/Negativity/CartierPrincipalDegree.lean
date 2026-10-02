module

public import Negativity.CurvePrincipalDegree
public import Negativity.CartierDegree
public import Negativity.CartierCurveMoving
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C] [CompactSpace C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C ≤ 1) (k : Type u) [Field k]
    (b : C ⟶ Spec (.of k)) [IsProper b]
    [Algebra (RatFunc k) C.functionField] [Algebra k C.functionField]
    [IsScalarTower k (RatFunc k) C.functionField]
    [FiniteDimensional (RatFunc k) C.functionField]
    [Algebra.IsSeparable (RatFunc k) C.functionField]
    (hbase : algebraMap k C.functionField = curveFunctionFieldBaseMap C k b)

include hd b hbase

omit [CompactSpace C] in
theorem curvePrincipalDivisor_allPoints_coefficient (a : C.functionFieldˣ) (x : C) :
    ((curvePrincipalDivisor C hn hd k b hbase a).mapDomain Subtype.val) x =
      if hx : Order.coheight x = 1 then schemeRationalOrder C hn x hx a else 0 := by
  classical
  by_cases hx : Order.coheight x = 1
  · rw [dite_eq_left hx]
    change ((curvePrincipalDivisor C hn hd k b hbase a).mapDomain Subtype.val)
      ((⟨x, hx⟩ : {x : C // Order.coheight x = 1}) : C) = _
    rw [Finsupp.mapDomain_apply_of_injective Subtype.val_injective]
    exact curvePrincipalDivisor_coefficient C hn hd k b hbase a ⟨x, hx⟩
  · rw [dite_eq_right hx]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨y, rfl⟩
    exact hx y.2

/-- Changing an actual Cartier representative by a global rational function
adds the actual principal divisor, with equality at every actual scheme point. -/
theorem cartierOrderDivisor_rationalTwist {ι : Type*} (A : CartierAtlas C ι)
    (a : C.functionFieldˣ) :
    cartierOrderDivisor C hn (A.rationalTwist a) =
      cartierOrderDivisor C hn A +
        (curvePrincipalDivisor C hn hd k b hbase a).mapDomain Subtype.val := by
  classical
  ext x
  rw [Finsupp.add_apply, cartierOrderDivisor_apply, cartierOrderDivisor_apply,
    curvePrincipalDivisor_allPoints_coefficient C hn hd k b hbase a x]
  by_cases hx : Order.coheight x = 1
  · simp only [CartierAtlas.coefficient, dite_eq_left hx, CartierAtlas.rationalTwist]
    have := hn x
    have := normal_codimensionOne_stalk_isDVR C x hx
    unfold schemeRationalOrder
    rw [dvr_rationalOrder_mul]
    dsimp only
    exact add_comm _ _
  · simp [CartierAtlas.coefficient, hx]

/-- Final theorem: on an actual proper normal curve over an algebraically
closed field, multiplying Cartier local equations by any nonzero rational
function preserves their total degree. The actual principal-divisor theorem
is used; degree-zero is not supplied as an assumption. This closes the
principal change of representative used in the Cartier moving construction,
under the explicitly compatible finite separable parameter. -/
theorem cartierTotalOrder_rationalTwist [IsAlgClosed k] {ι : Type*}
    (A : CartierAtlas C ι) (a : C.functionFieldˣ) :
    cartierTotalOrder C hn (A.rationalTwist a) = cartierTotalOrder C hn A := by
  have hz := (proper_normal_curve_principal_degree_zero C hn hd k b hbase a).2
  have he := cartierOrderDivisor_rationalTwist C hn hd k b hbase A a
  change (cartierOrderDivisor C hn (A.rationalTwist a)).degree =
    (cartierOrderDivisor C hn A).degree
  rw [he, map_add, Finsupp.degree_mapDomain, hz, add_zero]

end
end Negativity
