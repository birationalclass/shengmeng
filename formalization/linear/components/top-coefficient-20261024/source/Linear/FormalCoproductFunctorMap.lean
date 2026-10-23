/- Copyright (c) 2026 Joel Riou. Released under Apache 2.0. -/
module
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
universe w u v u₂ v₂
namespace CategoryTheory
/- Minimal inspected adaptation of Joel Riou mathlib4,commit04b574a2dc239b7964d235d5f66e31c37162b449. Apache2.0. Native objects retained;private continuation,NOT a completed Cech/native-H comparison. -/
namespace Functor

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D)

/-- The functor `FormalCoproduct C ⥤ FormalCoproduct D` that is induced
by a functor `C ⥤ D`. -/
@[simps]
def mapFormalCoproduct : FormalCoproduct.{w} C ⥤ FormalCoproduct.{w} D where
  obj X :=
    { I := X.I
      obj := F.obj ∘ X.obj }
  map f :=
    { f := f.f
      φ i := F.map (f.φ i) }

end Functor

end CategoryTheory
