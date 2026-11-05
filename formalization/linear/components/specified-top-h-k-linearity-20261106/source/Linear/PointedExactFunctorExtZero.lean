module
public import Linear.PointedExactFunctorExtMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {O : C} {P : D} (e : P ⟶ F.obj O)
/-- In degree zero the actual derived pointed map is exactly the original Hom map. -/
theorem pointedExactFunctorExtMap_zero_homEquiv (M : C) (x : Ext.{w} O M 0) :
    Ext.addEquiv₀ (pointedExactFunctorExtMap F e M 0 x) =
      e ≫ F.map (Ext.addEquiv₀ x) := by
  obtain ⟨a,rfl⟩ := (Ext.mk₀_bijective O M).surjective x
  change Ext.homEquiv₀ ((Ext.mk₀ e).comp ((Ext.mk₀ a).mapExactFunctor F) (zero_add 0)) =
    e ≫ F.map (Ext.homEquiv₀ (Ext.mk₀ a))
  rw [Ext.mapExactFunctor_mk₀,Ext.mk₀_comp_mk₀]
  change Ext.homEquiv₀ (Ext.homEquiv₀.symm (e ≫ F.map a)) =
    e ≫ F.map (Ext.homEquiv₀ (Ext.homEquiv₀.symm a))
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
end LinearStudy
