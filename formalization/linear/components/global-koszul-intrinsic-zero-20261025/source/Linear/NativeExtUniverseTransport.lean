module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Localization
universe u v w₁ w₂ d
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasExt.{w₁} A] [HasExt.{w₂} A]
variable (X Y : A) (q : ℕ)

/-- Native universe change for the SAME actual Ext group,not a new class
or a different resolution. Reuse SmallShiftedHom.chgUniv. -/
def nativeExtUniverseEquiv : Ext.{w₁} X Y q ≃ Ext.{w₂} X Y q :=
  SmallShiftedHom.chgUniv.{w₂}

/-- The SAME derived-category morphism is retained under universe change. -/
theorem nativeExtUniverseEquiv_hom [HasDerivedCategory.{d} A]
    (e : Ext.{w₁} X Y q) :
    (nativeExtUniverseEquiv.{u,v,w₁,w₂} X Y q e).hom = e.hom :=
  SmallShiftedHom.equiv_chgUniv.{w₂} DerivedCategory.Q e

/-- Universe change preserves addition of actual classes. -/
def nativeExtUniverseAddEquiv : Ext.{w₁} X Y q ≃+ Ext.{w₂} X Y q where
  toEquiv := nativeExtUniverseEquiv.{u,v,w₁,w₂} X Y q
  map_add' e e' := by
    letI := HasDerivedCategory.standard A
    apply Ext.homEquiv.injective
    change (nativeExtUniverseEquiv.{u,v,w₁,w₂} X Y q (e+e')).hom =
      (nativeExtUniverseEquiv.{u,v,w₁,w₂} X Y q e + nativeExtUniverseEquiv.{u,v,w₁,w₂} X Y q e').hom
    simp only [nativeExtUniverseEquiv_hom,Ext.add_hom]

/-- Coefficient/source composition of the SAME classes commutes with
native universe change. No Ext identity is a premise. -/
theorem nativeExtUniverseEquiv_comp {X Y Z : A} {a b c : ℕ}
    (e : Ext.{w₁} X Y a) (f : Ext.{w₁} Y Z b) (h : a+b=c) :
    (nativeExtUniverseEquiv.{u,v,w₁,w₂} X Z c (e.comp f h) : Ext.{w₂} X Z c) =
      (nativeExtUniverseEquiv.{u,v,w₁,w₂} X Y a e).comp (nativeExtUniverseEquiv.{u,v,w₁,w₂} Y Z b f) h := by
  letI := HasDerivedCategory.standard A
  apply Ext.homEquiv.injective
  simp only [nativeExtUniverseEquiv_hom,Ext.comp_hom]

theorem nativeExtUniverseEquiv_mk₀ {X Y : A} (f : X ⟶ Y) :
    (nativeExtUniverseEquiv.{u,v,w₁,w₂} X Y 0 (Ext.mk₀ f : Ext.{w₁} X Y 0) : Ext.{w₂} X Y 0) = Ext.mk₀ f := by
  letI := HasDerivedCategory.standard A
  apply Ext.homEquiv.injective
  change (nativeExtUniverseEquiv.{u,v,w₁,w₂} X Y 0 (Ext.mk₀ f : Ext.{w₁} X Y 0)).hom =
    (Ext.mk₀ f : Ext.{w₂} X Y 0).hom
  simp only [nativeExtUniverseEquiv_hom,Ext.mk₀_hom]

end LinearStudy
