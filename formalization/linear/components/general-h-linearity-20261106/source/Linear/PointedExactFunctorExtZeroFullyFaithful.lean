module
public import Linear.PointedExactFunctorExtZero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u v u' v' w w'
/-- A fully faithful exact functor with an actual isomorphic pointed source has a bijective
native Ext comparison in degree zero. No higher comparison or acyclicity is assumed. -/
theorem pointedExactFunctorExtMap_zero_bijective_of_fullyFaithful
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] {O : C} {P : D} (e : P ⟶ F.obj O) [IsIso e]
    (M : C) : Function.Bijective (pointedExactFunctorExtMap F e M 0) := by
  constructor
  · intro x y hxy
    apply Ext.addEquiv₀.injective
    apply F.map_injective
    apply (cancel_epi e).mp
    simpa only [pointedExactFunctorExtMap_zero_homEquiv] using congrArg Ext.addEquiv₀ hxy
  · intro y
    let f : O ⟶ M := F.preimage (inv e ≫ Ext.addEquiv₀ y)
    refine ⟨Ext.mk₀ f,?_⟩
    apply Ext.addEquiv₀.injective
    rw [pointedExactFunctorExtMap_zero_homEquiv]
    change e ≫ F.map (Ext.homEquiv₀ (Ext.homEquiv₀.symm f)) = Ext.addEquiv₀ y
    rw [Equiv.apply_symm_apply]
    simp [f]
end LinearStudy