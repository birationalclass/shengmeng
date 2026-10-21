module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
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
/-- The actual exact-functor Ext map,precomposed with a fixed original source morphism. -/
def pointedExactFunctorExtMap (M : C) (n : ℕ) :
    Ext.{w} O M n →+ Ext.{w'} P (F.obj M) n :=
  ((Ext.mk₀ e).precomp (F.obj M) (zero_add n)).comp (F.mapExtAddHom O M n)

/-- The same pointed map commutes with every actual coefficient morphism. -/
theorem pointedExactFunctorExtMap_postcompose {M N : C} (f : M ⟶ N) (n : ℕ)
    (x : Ext.{w} O M n) :
    pointedExactFunctorExtMap F e N n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (pointedExactFunctorExtMap F e M n x).comp (Ext.mk₀ (F.map f)) (add_zero n) := by
  change (Ext.mk₀ e).comp ((x.comp (Ext.mk₀ f) (add_zero n)).mapExactFunctor F) (zero_add n) = _
  rw [Ext.mapExactFunctor_comp,Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)).symm

/-- The pointed map commutes with the SAME covariant derived connecting class. -/
theorem pointedExactFunctorExtMap_boundary {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (x : Ext.{w} O S.X₃ n) :
    pointedExactFunctorExtMap F e S.X₁ (n+1) (x.comp hS.extClass rfl) =
      (pointedExactFunctorExtMap F e S.X₃ n x).comp (hS.map_of_exact F).extClass rfl := by
  change (Ext.mk₀ e).comp ((x.comp hS.extClass rfl).mapExactFunctor F) (zero_add (n+1)) = _
  rw [Ext.mapExactFunctor_comp,Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm
end LinearStudy
