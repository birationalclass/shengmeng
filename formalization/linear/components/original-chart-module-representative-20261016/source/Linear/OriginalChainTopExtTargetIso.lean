module
public import Linear.CochainResolutionTargetIso
public import Linear.ChainTopExtExactFunctorCompatibility
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe v u w d
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Actual chain-to-cochain conversion preserves composition with the
SAME target morphism,including the native single-complex comparisons. -/
theorem originalChainAugmentationAsCochain_target_comp
    (C : ChainComplex A ℕ) {E Q : A}
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) (g : E ⟶ Q) :
    originalChainAugmentationAsCochain C (alpha ≫ (ChainComplex.single₀ A).map g) =
      originalChainAugmentationAsCochain C alpha ≫
        (CochainComplex.singleFunctor A 0).map g := by
  apply HomologicalComplex.to_single_hom_ext
  simp [originalChainAugmentationAsCochain,Functor.map_comp,
    ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (show ComplexShape.embeddingDownNat.f 0 = (0:ℤ) by simp),
    HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.single_map_f_self,CochainComplex.singleFunctor,Category.assoc]

variable [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- The actual original CHAIN Ext roof transforms by the native degree-zero
Ext action of its target iso. The SAME augmentation and top functional
are retained;the desired class equality is proved,not assumed. -/
theorem originalChainTopExtClass_targetIso
    (C : ChainComplex A ℕ) {E Q M : A} (r : ℕ) (theta : E ≅ Q)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :
    (Ext.mk₀ theta.hom).comp
      (originalChainTopExtClass C r
        (alpha ≫ (ChainComplex.single₀ A).map theta.hom) a ha) (zero_add _) =
      originalChainTopExtClass C r alpha a ha := by
  letI := originalChainAugmentationAsCochain_quasiIso C alpha
  letI := originalChainAugmentationAsCochain_quasiIso C
    (alpha ≫ (ChainComplex.single₀ A).map theta.hom)
  rw [originalChainTopExtClass_eq_cochain,originalChainTopExtClass_eq_cochain]
  simpa only [originalChainAugmentationAsCochain_target_comp] using
    cochainResolutionExtClass_targetIso (originalChainAsCochain C) r theta
      (originalChainAugmentationAsCochain C alpha) (originalChainTopShiftedCocycle C r a ha)

end LinearStudy
