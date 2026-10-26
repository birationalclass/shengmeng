module
public import Linear.InjectiveCochainDegreeZeroClass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
/-- The SAME natural-indexed augmentation cocycle represents native Ext.mk0 of the actual morphism. -/
theorem injectiveNativeExtMk_ofHom {P N : A} (I : InjectiveResolution N)
    (a : P ⟶ N) (ha : (a ≫ I.ι.f 0) ≫ I.cocomplex.d 0 1 = 0) :
    I.extMk (a ≫ I.ι.f 0) 1 rfl ha = Ext.mk₀ a := by
  have h0 : (a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0) =
      (a ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv := by
    rw [I.ι'_f_zero]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
  have hclosed : ((a ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv) ≫
      I.cochainComplex.d 0 1 = 0 := by
    erw [I.cochainComplex_d 0 1 0 1 rfl rfl]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
    simpa only [Category.assoc,zero_comp] using congrArg
      (fun z => z ≫ (I.cochainComplexXIso 1 1 rfl).inv) ha
  have hclosed' : (a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫
      I.ι'.f 0) ≫ I.cochainComplex.d 0 1 = 0 := by rw [h0]; exact hclosed
  have he : Cocycle.fromSingleMk
        ((a ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv) (zero_add 0) 1 rfl hclosed =
      Cocycle.fromSingleMk
        (a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ I.ι'.f 0)
        (zero_add 0) 1 rfl hclosed' := by
    ext : 1
    exact congrArg (fun z => Cochain.fromSingleMk z (zero_add 0)) h0.symm
  dsimp only [InjectiveResolution.extMk]
  erw [he]
  exact injectiveCochainClass_zero I a hclosed'
end LinearStudy
