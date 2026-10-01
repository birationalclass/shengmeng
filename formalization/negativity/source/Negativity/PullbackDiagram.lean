module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory
universe u

/-- Pullbacks of actual sheaves of modules agree around the curve/image
commutative square. No intersection-number identity is assumed here. -/
theorem curve_square_pullback_iso {C X B Y : Scheme.{u}}
    (i : C ⟶ X) (f : X ⟶ Y) (h : C ⟶ B) (j : B ⟶ Y)
    (square : i ≫ f = h ≫ j) (L : Y.Modules) :
    Nonempty (((Scheme.Modules.pullback i).obj
      ((Scheme.Modules.pullback f).obj L)) ≅
      ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback j).obj L))) := by
  exact ⟨((Scheme.Modules.pullbackComp i f).app L) ≪≫
    ((Scheme.Modules.pullbackCongr square).app L) ≪≫
    ((Scheme.Modules.pullbackComp h j).symm.app L)⟩

end Negativity
