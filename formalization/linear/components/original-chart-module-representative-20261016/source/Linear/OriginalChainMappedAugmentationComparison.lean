module
public import Linear.AdditiveFunctorExtendSingleCompatibility
public import Linear.CochainResolutionExactFunctorObjects
public import Linear.ChainResolutionAsCochain
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe v u v' u'
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive]

/-- The ACTUAL comparison for the original chain-to-cochain conversion,
constructed from native zero extension,not supplied as a certificate. -/
def additiveFunctorOriginalChainCochainIso (C : ChainComplex A ℕ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (originalChainAsCochain C) ≅
      originalChainAsCochain ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) :=
  additiveFunctorExtendComplexIso F C ComplexShape.embeddingDownNat

/-- Map the SAME original chain augmentation and retain the native
single-complex comparison. This is an actual map,not a proof. -/
def mappedOriginalChainAugmentation (C : ChainComplex A ℕ) {E : A}
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C ⟶
      (ChainComplex.single₀ B).obj (F.obj E) :=
  (F.mapHomologicalComplex (ComplexShape.down ℕ)).map alpha ≫
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app E

/-- The ACTUAL mapped original augmentation agrees through the
constructed chain/cochain comparison. Every single-complex comparison
is retained. No desired Ext identity or augmentation equality is assumed. -/
theorem mappedOriginalChainAugmentation_asCochain
    (C : ChainComplex A ℕ) {E : A} (alpha : C ⟶ (ChainComplex.single₀ A).obj E) :
    mappedCochainResolutionAugmentation F (originalChainAsCochain C)
        (originalChainAugmentationAsCochain C alpha) =
      (additiveFunctorOriginalChainCochainIso F C).hom ≫
        originalChainAugmentationAsCochain ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C)
          (mappedOriginalChainAugmentation F C alpha) := by
  have hs := additiveFunctorExtendSingleIso_compatibility F ComplexShape.embeddingDownNat E 0 0 (by simp)
  have hn := additiveFunctorExtendComplexIso_naturality F alpha ComplexShape.embeddingDownNat
  simp only [mappedCochainResolutionAugmentation,originalChainAugmentationAsCochain,
    mappedOriginalChainAugmentation,additiveFunctorOriginalChainCochainIso,
    ComplexShape.Embedding.extendFunctor_map,Functor.map_comp,
    HomologicalComplex.extendMap_comp,originalChainAsCochain,Functor.mapCochainComplexSingleFunctor,Category.assoc]
  erw [hs,← reassoc_of% hn]

end LinearStudy