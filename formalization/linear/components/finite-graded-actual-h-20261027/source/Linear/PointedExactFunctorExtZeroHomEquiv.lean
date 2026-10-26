module
public import Linear.PointedExactFunctorExtZero
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u v u' v' w w'
/-- An ACTUAL Hom equivalence identified with the actual pointed Hom map gives
bijectivity of the SAME derived exact-functor Ext map in degree zero. -/
theorem pointedExactFunctorExtMap_zero_bijective_of_homEquiv
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {O : C} {P : D} (e : P ⟶ R.obj O) (M : C)
    (E : (O ⟶ M) ≃ (P ⟶ R.obj M))
    (hE : ∀ a : O ⟶ M, e ≫ R.map a = E a) :
    Function.Bijective (pointedExactFunctorExtMap R e M 0) := by
  constructor
  · intro x y hxy
    apply Ext.addEquiv₀.injective
    apply E.injective
    have h := congrArg Ext.addEquiv₀ hxy
    rw [pointedExactFunctorExtMap_zero_homEquiv,
      pointedExactFunctorExtMap_zero_homEquiv] at h
    exact (hE _).symm.trans (h.trans (hE _))
  · intro y
    let a := E.symm (Ext.addEquiv₀ y)
    refine ⟨Ext.mk₀ a,?_⟩
    apply Ext.addEquiv₀.injective
    rw [pointedExactFunctorExtMap_zero_homEquiv]
    change e ≫ R.map (Ext.homEquiv₀ (Ext.homEquiv₀.symm a)) = Ext.addEquiv₀ y
    rw [Equiv.apply_symm_apply,hE]
    exact E.apply_symm_apply _
end LinearStudy
