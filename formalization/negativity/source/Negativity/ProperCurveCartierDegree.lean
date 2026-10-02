module

public import Negativity.CurveCartierDegree
public import Negativity.ProperCurveFinite
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Finite-map auxiliary theorem: the actual Cartier pullback degree formula on complete
normal integral curves over an algebraically closed field of arbitrary
characteristic. Compactness is derived from properness, actual pullback
charts and equations are supplied as outputs, and no separability, fiber
list, weight, order compatibility or projection identity is an input. -/
theorem complete_normal_curve_finite_cartier_pullback_degree
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [IsProper b]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdX : Order.krullDim X = 1) (hdY : Order.krullDim Y = 1)
    {ι : Type*} (A : CartierAtlas Y ι) :
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ b)
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    ∃ B : CartierAtlas X X,
      (∀ z : X, B.chart z ≤ f ⁻¹ᵁ A.chart (A.covers (f z)).choose ∧ z ∈ B.chart z ∧
        B.equation z = Units.map (dominantFunctionFieldMap f).toMonoidHom
          (A.equation (A.covers (f z)).choose)) ∧
      cartierTotalOrder X hnX B =
        (Module.finrank Y.functionField X.functionField : ℤ) * cartierTotalOrder Y hnY A := by
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ b)
  exact finite_normal_curve_cartier_pullback_degree f k b hnX hnY hdX.le hdY.le A

/-- Final theorem: the actual global Cartier pullback degree formula for
proper dominant morphisms of complete normal integral curves. Finiteness,
compactness, actual fiber multiplicities and Cartier compatibility are
all derived. Arbitrary characteristic and inseparable degree are retained. -/
theorem complete_normal_curve_cartier_pullback_degree
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [IsProper b]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdX : Order.krullDim X = 1) (hdY : Order.krullDim Y = 1)
    {ι : Type*} (A : CartierAtlas Y ι) :
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ b)
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    ∃ B : CartierAtlas X X,
      (∀ z : X, B.chart z ≤ f ⁻¹ᵁ A.chart (A.covers (f z)).choose ∧ z ∈ B.chart z ∧
        B.equation z = Units.map (dominantFunctionFieldMap f).toMonoidHom
          (A.equation (A.covers (f z)).choose)) ∧
      cartierTotalOrder X hnX B =
        (Module.finrank Y.functionField X.functionField : ℤ) * cartierTotalOrder Y hnY A := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ b)
  have : IsNoetherian X := ⟨⟩
  have := proper_dominant_integral_curve_isFinite f hdX hdY
  exact complete_normal_curve_finite_cartier_pullback_degree f k b hnX hnY hdX hdY A

end Negativity
