module
public import Linear.AdditiveFunctorEndRingHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u v w
/-- Apply an actual functor to an ORIGINAL coefficient scalar square.
This is a generic pointwise interface;no derived sheaf object is unfolded. -/
theorem additiveFunctor_map_commuting_apply {C : Type u} [Category.{v} C]
    (F : C ⥤ AddCommGrpCat.{w}) {M N : C} (f : M ⟶ N)
    (sM : M ⟶ M) (sN : N ⟶ N) (h : sM ≫ f = f ≫ sN) (x : F.obj M) :
    F.map f (F.map sM x) = F.map sN (F.map f x) := by
  have hh : F.map sM ≫ F.map f = F.map f ≫ F.map sN := by
    rw [← F.map_comp,h,F.map_comp]
  exact ConcreteCategory.congr_hom hh x
end LinearStudy
