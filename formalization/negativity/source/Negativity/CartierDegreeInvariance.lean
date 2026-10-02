module

public import Negativity.CurveFunctionField
public import Negativity.CartierPrincipalDegree
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Final theorem: principal changes of actual Cartier local equations
preserve degree on an actual complete normal curve. The separating parameter
and compactness are derived from the Scheme hypotheses. In particular the
Cartier moving construction preserves degree in arbitrary characteristic. -/
theorem complete_normal_curve_cartier_degree_invariant
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (b : C ⟶ Spec (.of k)) [IsProper b] [Algebra k C.functionField]
    (hbase : algebraMap k C.functionField = curveFunctionFieldBaseMap C k b)
    {ι : Type*} (A : CartierAtlas C ι) (a : C.functionFieldˣ) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace b
    cartierTotalOrder C hn (A.rationalTwist a) = cartierTotalOrder C hn A := by
  obtain ⟨f, hfin, hsep⟩ := finiteType_curve_exists_separating_parameter C hd k b hbase
  let : Algebra (RatFunc k) C.functionField := f.toRingHom.toAlgebra
  have : IsScalarTower k (RatFunc k) C.functionField :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have := hfin
  have := hsep
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace b
  exact cartierTotalOrder_rationalTwist C hn hd.le k b hbase A a

end Negativity
