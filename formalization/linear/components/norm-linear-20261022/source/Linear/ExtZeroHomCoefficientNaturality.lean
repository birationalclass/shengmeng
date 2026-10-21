module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
/-- Native degree-zero Ext/Hom equivalence commutes with the actual coefficient map. -/
theorem extZeroHomEquiv_postcompose (O : A) {F G : A} (f : F ⟶ G) (x : Ext O F 0) :
    Ext.addEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0)) = Ext.addEquiv₀ x ≫ f := by
  delta Ext.addEquiv₀
  apply (Ext.mk₀_bijective O G).injective
  simp only [AddEquiv.coe_mk,Ext.mk₀_homEquiv₀_apply,← Ext.mk₀_comp_mk₀]
end LinearStudy
