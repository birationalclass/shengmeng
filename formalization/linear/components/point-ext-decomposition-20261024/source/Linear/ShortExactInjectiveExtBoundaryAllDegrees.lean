module
public import Linear.CochainConeLiftTriangleDegrees
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
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

/-- Compute the native contravariant Ext boundary in every nonnegative degree
from the actual cochain lift equations and any injective resolution. -/
theorem shortExactInjectiveExtBoundary_allDegrees
    (S : ShortComplex A) (hS : S.ShortExact) {N : A} (I : InjectiveResolution N)
    (q : ℕ)
    (a : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₁) I.cochainComplex (q : ℤ))
    (b : Cochain ((CochainComplex.singleFunctor A 0).obj S.X₂) I.cochainComplex (q : ℤ))
    (c : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₃) I.cochainComplex ((q+1 : ℕ) : ℤ))
    (hb : (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.f)).comp b
      (zero_add (q : ℤ)) = a.val)
    (hc : δ (q : ℤ) ((q+1 : ℕ) : ℤ) b =
      (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.g)).comp c.val
        (zero_add ((q+1 : ℕ) : ℤ))) :
    Ext.δ hS q (q+1) rfl (I.extEquivCohomologyClass.symm (CohomologyClass.mk a)) =
      (I.extEquivCohomologyClass (n := q+1)).symm (CohomologyClass.mk c) := by
  letI := HasDerivedCategory.standard A
  let T := S.map (CochainComplex.singleFunctor A 0)
  let alpha := CochainComplex.mappingCone.descShortComplex T
  haveI := CochainComplex.mappingCone.quasiIso_descShortComplex
    (hS.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℤ) 0))
  have h := cochainConeLiftTriangle_degrees T I.cochainComplex (q : ℤ)
    ((q+1 : ℕ) : ℤ) (by omega) a b c hb hc
  simp only [Cocycle.equivHomShift_symm_precomp] at h
  rw [Units.smul_def,ShiftedHom.map_smul,ShiftedHom.map_comp] at h
  simp only [ShiftedHom.map,CategoryTheory.Functor.map_comp,Category.assoc] at h
  have hr := congrArg (fun f => inv (DerivedCategory.Q.map alpha) ≫ f ≫
    (shiftFunctor (DerivedCategory A) ((q+1 : ℕ) : ℤ)).map (inv (DerivedCategory.Q.map I.ι'))) h
  simp only [Category.assoc,IsIso.inv_hom_id_assoc] at hr
  apply Ext.ext
  rw [Ext.δ_apply]
  change Ext.homAddEquiv (_ • _) = _
  rw [Units.smul_def,map_zsmul,Ext.homAddEquiv_apply,Ext.comp_hom,
    ShortComplex.ShortExact.extClass_hom,I.extEquivCohomologyClass_symm_mk_hom,
    I.extEquivCohomologyClass_symm_mk_hom]
  simp only [DerivedCategory.singleFunctorIsoCompQ_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_inv_app,ShiftedHom.mk₀_id_comp,Category.comp_id]
  rw [← ShiftedHom.comp_assoc _ _ _
    (show (q : ℤ)+1=((q+1 : ℕ) : ℤ) by omega) (zero_add (q : ℤ)) (by omega)]
  simp only [ShiftedHom.comp_mk₀]
  dsimp only [ShortComplex.ShortExact.singleδ,DerivedCategory.triangleOfSESδ]
  simpa only [T,alpha,CochainComplex.mappingCone.triangle,Pretriangulated.Triangle.mk_obj₁,
    Pretriangulated.Triangle.mk_mor₃,ShiftedHom.comp,ShiftedHom.map,ShiftedHom,ShortComplex.map,
    Nat.cast_one,Int.cast_ofNat_Int,← DerivedCategory.Q_obj_single_obj,
    CochainComplex.singleFunctor,CochainComplex.singleFunctors,Category.assoc,
    CategoryTheory.Functor.map_inv,Preadditive.zsmul_comp,Preadditive.comp_zsmul,
    IsIso.inv_hom_id_assoc,Category.comp_id,CategoryTheory.Functor.map_id] using hr.symm

end LinearStudy
