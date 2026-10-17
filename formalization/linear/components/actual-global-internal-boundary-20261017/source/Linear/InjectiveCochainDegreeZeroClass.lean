module
public import Linear.CochainCocycleOfHomShifted
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- ACTUAL augmentation cocycle represents the native Ext degree-zero map. -/
theorem injectiveCochainClass_ofHom {P N : A} (I : InjectiveResolution N) (g : P ⟶ N) :
    (I.extEquivCohomologyClass (n := 0)).symm (CohomologyClass.mk
      (Cocycle.ofHom ((CochainComplex.singleFunctor A 0).map g ≫ I.ι'))) = Ext.mk₀ g := by
  letI := HasDerivedCategory.standard A
  apply Ext.ext
  rw [I.extEquivCohomologyClass_symm_mk_hom]
  erw [cochainCocycleOfHom_shifted,ShiftedHom.map_mk₀,Ext.mk₀_hom]
  simp only [ShiftedHom.mk₀_comp_mk₀,DerivedCategory.singleFunctorIsoCompQ_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_inv_app,CategoryTheory.Functor.map_comp,
    Category.id_comp,Category.assoc,IsIso.hom_inv_id_assoc,Category.comp_id]
  erw [DerivedCategory.Q_map_single_map A 0 g]
  congr 1 <;> simp only [Category.comp_id]

/-- The physical degree-zero component retains all single-complex unit
maps and represents EXACTLY the original morphism as native Ext.mk0. -/
theorem injectiveCochainClass_zero {P N : A} (I : InjectiveResolution N) (g : P ⟶ N)
    (hf : (g ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0) ≫
      I.cochainComplex.d 0 1 = 0) :
    (I.extEquivCohomologyClass (n := 0)).symm (CohomologyClass.mk
      (Cocycle.fromSingleMk
        (g ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0)
        (zero_add 0) 1 rfl hf)) = Ext.mk₀ g := by
  have hc : Cocycle.fromSingleMk
      (g ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0)
      (zero_add 0) 1 rfl hf =
      Cocycle.ofHom ((CochainComplex.singleFunctor A 0).map g ≫ I.ι') := by
    ext : 1
    change Cochain.fromSingleMk _ (zero_add 0) = Cochain.ofHom _
    apply (Cochain.fromSingleEquiv (p := 0) (q := 0) (n := 0) (zero_add 0)).injective
    simp [Cochain.fromSingleEquiv,CochainComplex.singleFunctor,CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self,Category.assoc]
  rw [hc]
  exact injectiveCochainClass_ofHom I g

end LinearStudy
