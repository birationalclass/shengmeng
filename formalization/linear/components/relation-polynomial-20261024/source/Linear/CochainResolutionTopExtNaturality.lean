/-
Adapted from mathlib CategoryTheory/Abelian/Projective/Ext.lean.
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the mathlib LICENSE.
-/
module
public import Linear.CochainResolutionExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
open CochainComplex.HomComplex
universe w w' v u
variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasExt.{w} A] [HasDerivedCategory.{w'} A]

/-- Pushforward of the ACTUAL resolution class is represented by
postcomposition of its SAME top functional. Adapt the native mathlib
ProjectiveResolution.extMk_comp_mk₀ shifted-Hom argument,using the
actual quasiiso roof without assuming projective resolution terms.
The original geometric support/restriction identification is separate. -/
theorem cochainResolutionTopExtClass_comp_mk₀ (K : CochainComplex A ℤ)
    {E M N : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (f : K.X (-(r : ℤ)) ⟶ M)
    (hf : K.d (-(r : ℤ)-1) (-(r : ℤ)) ≫ f = 0) (g : M ⟶ N) :
    (cochainResolutionTopExtClass K r alpha f hf).comp (Ext.mk₀ g) (add_zero _) =
      cochainResolutionTopExtClass K r alpha (f ≫ g) (by simp [reassoc_of% hf]) := by
  apply Ext.ext
  simp only [cochainResolutionTopExtClass,Ext.comp_hom,Ext.mk₀_hom,
    cochainResolutionExtClass_hom]
  rw [Cocycle.toSingleMk_postcomp _ _ _ _ hf g,
    Cocycle.equivHomShift_symm_postcomp,
    ← ShiftedHom.comp_mk₀ _ 0 rfl,
    ShiftedHom.map_comp,ShiftedHom.map_mk₀,
    ShiftedHom.comp_assoc _ _ _ (add_zero _) (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ (zero_add _) (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ (zero_add _) (zero_add _) (by simp),
    ShiftedHom.mk₀_comp_mk₀,ShiftedHom.mk₀_comp_mk₀,← NatTrans.naturality]
  dsimp

end LinearStudy
