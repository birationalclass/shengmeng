module
public import Linear.CochainConeLiftTriangleEquation
public import Linear.CochainShortExactRoofClass
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option pp.universes true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- A native short-exact roof pushed by a is MINUS the actual injective cocycle
obtained from the SAME degree-zero cochain lift. Only raw lift equations are
premises;the desired Ext-class equality is PROVED. The original arbitrary-r
Koszul lifts and quotient augmentation are separate obligations. -/
theorem shortExactRoof_comp_eq_neg_injectiveCocycle
    (S : ShortComplex A) (hS : S.ShortExact) {N : A} (I : InjectiveResolution N)
    (a : S.X₁ ⟶ N)
    (b : Cochain ((CochainComplex.singleFunctor A 0).obj S.X₂) I.cochainComplex 0)
    (c : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₃) I.cochainComplex 1)
    (hb : (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.f)).comp b (zero_add 0) =
      Cochain.ofHom ((CochainComplex.singleFunctor A 0).map a ≫ I.ι'))
    (hc : δ 0 1 b =
      (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.g)).comp c.val (zero_add 1)) :
    (cochainShortExactRoofClass S hS).comp (Ext.mk₀ a) (add_zero 1) =
      -(I.extEquivCohomologyClass.symm (CohomologyClass.mk c)) := by
  rw [cochainShortExactRoofClass_eq_extClass]
  letI := HasDerivedCategory.standard A
  let T := S.map (CochainComplex.singleFunctor A 0)
  let alpha := CochainComplex.mappingCone.descShortComplex T
  haveI := CochainComplex.mappingCone.quasiIso_descShortComplex
    (hS.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℤ) 0))
  have h := cochainConeLiftTriangleEquation T I.cochainComplex
    ((CochainComplex.singleFunctor A 0).map a ≫ I.ι') b c hb hc
  have hr := congrArg (fun f => inv (DerivedCategory.Q.map alpha) ≫ f ≫
    (shiftFunctor (DerivedCategory A) (1 : ℤ)).map (inv (DerivedCategory.Q.map I.ι'))) h
  simp only [CategoryTheory.Functor.map_comp,Category.assoc,
    CategoryTheory.Functor.map_inv,IsIso.hom_inv_id,
    Category.comp_id,Preadditive.comp_neg,Preadditive.neg_comp] at hr
  apply Ext.ext
  rw [Ext.comp_hom,Ext.mk₀_hom,ShortComplex.ShortExact.extClass_hom,Ext.neg_hom,
    I.extEquivCohomologyClass_symm_mk_hom]
  simp only [ShiftedHom.comp_mk₀,ShiftedHom.mk₀_comp,
    DerivedCategory.singleFunctorIsoCompQ_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_inv_app,Category.id_comp]
  erw [Category.comp_id]
  erw [← DerivedCategory.Q_map_single_map A 0 a]
  dsimp only [ShortComplex.ShortExact.singleδ,DerivedCategory.triangleOfSESδ]
  simpa only [T,alpha,ShiftedHom,ShortComplex.map,Nat.cast_one,Int.cast_ofNat_Int,
    ← DerivedCategory.Q_obj_single_obj,CochainComplex.singleFunctor,
    CochainComplex.singleFunctors,Category.assoc,CategoryTheory.Functor.map_inv,
    Preadditive.neg_comp,IsIso.inv_hom_id_assoc] using hr

end LinearStudy
