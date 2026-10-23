module
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Module.Hom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u v u' v'
/-- Bundle native additive F.map and native F.mapEnd into the SAME map
on endomorphism rings, retaining actual composition and addition. -/
def additiveFunctorEndRingHom {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (X : C) : End X →+* End (F.obj X) where
  __ := F.mapEnd X
  map_zero' := F.map_zero X X
  map_add' _ _ := F.map_add
/-- The native AddCommGrpCat endomorphism is its ORIGINAL additive map.
No comparison equivalence or choice is used. -/
def addCommGroupEndRingHom (A : AddCommGrpCat.{u}) : End A →+* AddMonoid.End A where
  toFun f := f.hom
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
end LinearStudy
