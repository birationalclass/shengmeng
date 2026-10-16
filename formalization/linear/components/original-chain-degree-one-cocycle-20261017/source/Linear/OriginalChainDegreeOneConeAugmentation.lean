module
public import Linear.OriginalChainDegreeOneConeMap
public import Linear.ChainActualCokernelAugmentation
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The ACTUAL first differential and its categorical quotient. -/
def originalChainFirstCokernelSequence (C : ChainComplex A ℕ) : ShortComplex A :=
  ShortComplex.mk (C.d 1 0) (cokernel.π (C.d 1 0)) (cokernel.condition _)

/-- The SAME original quotient augmentation is retained by the actual
chain-to-cone map. There is no assumed augmentation compatibility square. -/
theorem originalChainDegreeOneConeMap_augmentation
    (C : ChainComplex A ℕ) (h : C.d 2 1 = 0) :
    originalChainDegreeOneConeMap C h ≫ CochainComplex.mappingCone.descShortComplex
      ((originalChainFirstCokernelSequence C).map (CochainComplex.singleFunctor A 0)) =
      originalChainAugmentationAsCochain C (originalChainCokernelAugmentation C) := by
  apply Cochain.ofHom_injective
  rw [Cochain.ofHom_comp]
  simp only [originalChainDegreeOneConeMap,originalChainFirstCokernelSequence,
    ShortComplex.map,CochainComplex.mappingCone.descShortComplex,
    CochainComplex.mappingCone.ofHom_lift,CochainComplex.mappingCone.ofHom_desc,
    CochainComplex.mappingCone.liftCochain_descCochain,Cochain.comp_zero,zero_add]
  rw [← Cochain.toSingleMk_postcomp]
  apply (Cochain.toSingleEquiv (show (0:ℤ)+0=0 by omega)).injective
  rw [Cochain.toSingleEquiv_toSingleMk]
  change (originalChainAsCochainXIso C 0 0 (by norm_num)).hom ≫
    cokernel.π (C.d 1 0) =
      (Cochain.ofHom (originalChainAugmentationAsCochain C
        (originalChainCokernelAugmentation C))).v 0 0 (add_zero 0) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (cokernel (C.d 1 0))).hom
  rw [Cochain.ofHom_v]
  simp only [originalChainAugmentationAsCochain,HomologicalComplex.comp_f,
    ComplexShape.Embedding.extendFunctor_map]
  rw [HomologicalComplex.extendMap_f _ _ (show -(0:ℤ)=0 by norm_num),
    HomologicalComplex.extendSingleIso_hom_f]
  simp [originalChainAsCochainXIso,originalChainCokernelAugmentation_f_zero,
    Category.assoc]

end LinearStudy
