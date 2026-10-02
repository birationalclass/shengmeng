module

public import Negativity.CurveFunctionField
public import Negativity.CurvePrincipalDegree
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Final theorem: every nonzero rational function on an actual complete
normal integral curve over an algebraically closed field has a finite
principal divisor, with its actual stalk orders as coefficients, and total
degree zero. Parameters and all places are constructed in the proof.
No separability, perfectness of k(t), place correspondence, or product
formula is an input. The characteristic is arbitrary. -/
theorem complete_normal_curve_principal_product_formula
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (b : C ⟶ Spec (.of k)) [IsProper b] [Algebra k C.functionField]
    (hbase : algebraMap k C.functionField = curveFunctionFieldBaseMap C k b)
    (a : C.functionFieldˣ) :
    ∃ D : {x : C // Order.coheight x = 1} →₀ ℤ,
      (∀ x, D x = schemeRationalOrder C hn x x.2 a) ∧ D.degree = 0 := by
  obtain ⟨f, hfin, hsep⟩ := finiteType_curve_exists_separating_parameter C hd k b hbase
  let : Algebra (RatFunc k) C.functionField := f.toRingHom.toAlgebra
  have : IsScalarTower k (RatFunc k) C.functionField :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have := hfin
  have := hsep
  exact ⟨curvePrincipalDivisor C hn hd.le k b hbase a,
    proper_normal_curve_principal_degree_zero C hn hd.le k b hbase a⟩

end Negativity
