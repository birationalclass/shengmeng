module
public import Negativity.ClosedPointFiberThickenings
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

def actualClosedFiberIdealMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (_hy : IsClosed ({y} : Set Y)) :
    f.fiber y ⟶ ((actualClosedPointIdeal Y y).comap f).subscheme :=
  pullback.map f (Y.fromSpecResidueField y) f
    (Y.fromSpecResidueField y).imageι (𝟙 X) (Y.fromSpecResidueField y).toImage (𝟙 Y)
    (by simp) (by simp) ≫
      ((actualClosedPointIdeal Y y).comapIso f).inv

instance actualClosedFiberIdealMap_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) : IsIso (actualClosedFiberIdealMap f y hy) := by
  let : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  dsimp [actualClosedFiberIdealMap]
  infer_instance

@[reassoc (attr := simp)]
theorem actual_closed_fiber_ideal_map_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) :
    actualClosedFiberIdealMap f y hy ≫ ((actualClosedPointIdeal Y y).comap f).subschemeι =
      f.fiberι y := by
  simp [actualClosedFiberIdealMap, pullback.map, IdealSheafData.comapIso_inv_subschemeι]
  change _ = pullback.fst f (Y.fromSpecResidueField y)
  dsimp only [Scheme.Hom.fiber, actualClosedPointIdeal, Scheme.Hom.imageι]
  rw [pullback.lift_fst]

/-- Final theorem: the actual scheme fiber over a closed point is
isomorphic to the actual pulled-back point-ideal subscheme, with its
actual immersion into the original scheme preserved. -/
theorem actual_closed_fiber_ideal_scheme_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (hy : IsClosed ({y} : Set Y)) :
    ∃ e : f.fiber y ≅ ((actualClosedPointIdeal Y y).comap f).subscheme,
      e.hom ≫ ((actualClosedPointIdeal Y y).comap f).subschemeι = f.fiberι y :=
  ⟨asIso (actualClosedFiberIdealMap f y hy), actual_closed_fiber_ideal_map_fac f y hy⟩

end
end Negativity
