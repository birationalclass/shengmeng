module
public import Linear.ModuleOrderedBaseCech
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open AlgebraicGeometry.Scheme.Modules
universe u
/-- The original ordered deletion has exactly the original succAbove values.
This small interface avoids repeatedly unfolding simplex-category homs. -/
theorem orderedCechIndex_delete_values {ι : Type u} [Preorder ι] {p : ℕ}
    (t : OrderedCechIndex ι (p+1)) (k : Fin (p+2)) :
    (t.delete k).1 = fun j => t.1 (k.succAbove j) := rfl
end LinearStudy
