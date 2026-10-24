module
public import Linear.CochainResolutionAugmentationZero
public import Linear.ChainResolutionTopExtClass
public import Linear.ChainActualCokernelTargetAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The actual n-to-minus-n conversion retains the SAME original zero
augmentation, including the two native single-object identifications. -/
theorem originalChainAugmentationAsCochain_f_zero (C : ChainComplex A ℕ) {E : A}
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) :
    (originalChainAugmentationAsCochain C alpha).f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).hom =
      (originalChainAsCochainXIso C 0 0 (by norm_num)).hom ≫ alpha.f 0 := by
  simp only [originalChainAugmentationAsCochain,HomologicalComplex.comp_f,
    ComplexShape.Embedding.extendFunctor_map]
  rw [HomologicalComplex.extendMap_f _ _ (show -(0:ℤ)=0 by norm_num),
    HomologicalComplex.extendSingleIso_hom_f]
  simp [originalChainAsCochainXIso,Category.assoc]

variable [HasExt.{w} A] [HasDerivedCategory.{d} A]
/-- Pulling back the SAME ORIGINAL positive Ext class along its ACTUAL
zero augmentation gives zero. No global projectivity is assumed. -/
theorem originalChainTopExtClass_augmentation_precomp_zero
    (C : ChainComplex A ℕ) {E N : A} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    (Ext.mk₀ (alpha.f 0)).comp
      (originalChainTopExtClass C r alpha a ha) (zero_add r) = 0 := by
  letI := originalChainAugmentationAsCochain_quasiIso C alpha
  haveI : (originalChainAsCochain C).IsStrictlyLE 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyLE (C.extend ComplexShape.embeddingDownNat) 0)
  have h := cochainResolutionExtClass_augmentation_precomp_zero
    (originalChainAsCochain C) r hr (originalChainAugmentationAsCochain C alpha)
    (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (CochainComplex.HomComplex.Cocycle.toSingleMk
        ((originalChainAsCochainXIso C (-(r : ℤ)) r rfl).hom ≫ a)
        (by simp) (-(r : ℤ)-1) (by omega) (by
          rw [originalChainAsCochain_d C (-(r : ℤ)-1) (-(r : ℤ))
            (r+1) r (by omega) rfl]
          simp only [Category.assoc,Iso.inv_hom_id_assoc,ha,comp_zero])))
  change (Ext.mk₀ ((originalChainAugmentationAsCochain C alpha).f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).hom)).comp
      (originalChainTopExtClass C r alpha a ha) (zero_add r) = 0 at h
  rw [originalChainAugmentationAsCochain_f_zero] at h
  have hh := congrArg (fun t =>
    (Ext.mk₀ (originalChainAsCochainXIso C 0 0 (by norm_num)).inv).comp t
      (zero_add r)) h
  simpa only [Ext.mk₀_comp_mk₀_assoc,Iso.inv_hom_id_assoc,Ext.comp_zero] using hh

/-- For the ORIGINAL quotient target the map in this zero identity is
literally cokernel.pi followed by the SAME constructed source iso e. -/
theorem originalChainTopExtClass_quotient_precomp_zero
    (C : ChainComplex A ℕ) {E N : A} (r : ℕ) (hr : 0 < r)
    (e : cokernel (C.d 1 0) ≅ E)
    (hAlpha : QuasiIso (originalChainCokernelTargetAugmentation C E e))
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    letI := hAlpha
    (Ext.mk₀ (cokernel.π (C.d 1 0) ≫ e.hom)).comp
      (originalChainTopExtClass C r (originalChainCokernelTargetAugmentation C E e) a ha)
        (zero_add r) = 0 := by
  letI := hAlpha
  simpa only [originalChainCokernelTargetAugmentation_f_zero] using
    originalChainTopExtClass_augmentation_precomp_zero C r hr
      (originalChainCokernelTargetAugmentation C E e) a ha
end LinearStudy
