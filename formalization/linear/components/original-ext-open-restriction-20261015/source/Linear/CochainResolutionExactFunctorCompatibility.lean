/-
Uses mathlib Algebra/Homology/DerivedCategory/Ext/Map.lean.
Copyright (c) 2025 Nailin Guan, Jingting Wang, Joël Riou.
Released under Apache 2.0 license as described in the mathlib LICENSE.
-/
module
public import Linear.CochainResolutionExactFunctorObjects
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe v u v' u' wA wB dA dB
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{wA} A] [HasDerivedCategory.{dA} A]
variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasExt.{wB} B] [HasDerivedCategory.{dB} B]
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Compare the SAME actual resolution roof after an exact functor with
native Ext.mapExactFunctor. This is the missing generic compatibility
needed before specializing to actual open restriction/stalk functors. -/
theorem cochainResolutionExtClass_mapExactFunctor
    (K : CochainComplex A ℤ) {E M : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (beta : ShiftedHom K ((CochainComplex.singleFunctor A 0).obj M) (r:ℤ)) :
    (cochainResolutionExtClass K r alpha beta).mapExactFunctor F =
      mappedCochainResolutionExtClass F K r alpha beta := by
  have ha :
      F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor A 0).obj E) ≫
          inv (F.mapDerivedCategory.map (DerivedCategory.Q.map alpha)) =
        inv (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map alpha)) ≫
          F.mapDerivedCategoryFactors.inv.app K := by
    apply (cancel_mono (F.mapDerivedCategory.map (DerivedCategory.Q.map alpha))).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hn :
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map alpha) ≫
            F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor A 0).obj E) =
          F.mapDerivedCategoryFactors.inv.app K ≫
            F.mapDerivedCategory.map (DerivedCategory.Q.map alpha) :=
      F.mapDerivedCategoryFactors.inv.naturality alpha
    rw [← hn]
    simp
  have hb := ShiftedHom.map_naturality beta F.mapDerivedCategoryFactors.hom
  simp only [ShiftedHom.map, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
    Functor.commShiftIso_comp_hom_app, Functor.comp_map, Functor.comp_obj,
    Functor.map_comp, Category.assoc] at hb
  apply Ext.ext
  simp only [mappedCochainResolutionExtClass, Ext.mapExactFunctor_hom,
    cochainResolutionExtClass_hom, mappedCochainResolutionAugmentation,
    mappedCochainResolutionCocycle, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
    ShiftedHom.map, Functor.map_comp, Functor.map_inv]
  simp only [Functor.mapDerivedCategorySingleFunctor_inv_app,
    Functor.mapDerivedCategorySingleFunctor_hom_app, IsIso.inv_comp,
    Functor.map_comp, Functor.map_inv, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc, Functor.map_id, Category.id_comp]
  rw [← Functor.commShiftIso_hom_naturality_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.mapDerivedCategory.map_comp_assoc
    ((shiftFunctor (DerivedCategory A) (r:ℤ)).map
      ((DerivedCategory.singleFunctorIsoCompQ A 0).inv.app M))
    ((shiftFunctor (DerivedCategory A) (r:ℤ)).map
      ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app M))]
  rw [← (shiftFunctor (DerivedCategory A) (r:ℤ)).map_comp, Iso.inv_hom_id_app]
  simp only [(shiftFunctor (DerivedCategory A) (r:ℤ)).map_id,
    F.mapDerivedCategory.map_id, Category.id_comp]
  erw [F.mapDerivedCategory.map_id]
  repeat' erw [Category.id_comp]
  erw [reassoc_of% ha, reassoc_of% hb]
  erw [Iso.inv_hom_id_app_assoc]
  erw [← Functor.commShiftIso_hom_naturality_assoc]
  simp [Functor.mapCochainComplexSingleFunctor]

end LinearStudy
