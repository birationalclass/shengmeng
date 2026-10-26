module
public import Linear.OriginalChainMappedTopCocycle
public import Linear.CochainResolutionSourceIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe v u v' u' w d
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Exactness DERIVES the mapped actual chain augmentation's quasiiso. -/
theorem mappedOriginalChainAugmentation_quasiIso
    (C : ChainComplex A ℕ) {E : A} (alpha : C ⟶ (ChainComplex.single₀ A).obj E)
    [QuasiIso alpha] : QuasiIso (mappedOriginalChainAugmentation F C alpha) := by
  dsimp [mappedOriginalChainAugmentation]
  infer_instance

variable [HasExt.{w} B] [HasDerivedCategory.{d} B]

/-- The ACTUAL mapped cochain roof equals the class of the SAME actual
mapped CHAIN complex,augmentation and functional,through the constructed
chain/cochain comparison. No desired Ext identity is an input. -/
theorem originalChainMappedTopExtClass_eq_mappedChain
    (C : ChainComplex A ℕ) {E M : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :
    letI := mappedOriginalChainAugmentation_quasiIso F C alpha
    originalChainMappedTopExtClass F C r alpha a ha =
      originalChainTopExtClass ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) r
        (mappedOriginalChainAugmentation F C alpha) (F.map a)
        (by change F.map (C.d _ _) ≫ F.map a = 0; rw [← F.map_comp,ha,F.map_zero]) := by
  letI := mappedOriginalChainAugmentation_quasiIso F C alpha
  letI := originalChainAugmentationAsCochain_quasiIso C alpha
  letI := originalChainAugmentationAsCochain_quasiIso
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) (mappedOriginalChainAugmentation F C alpha)
  rw [originalChainTopExtClass_eq_cochain]
  dsimp only [originalChainMappedTopExtClass,mappedCochainResolutionExtClass]
  simpa only [mappedOriginalChainAugmentation_asCochain,mappedOriginalChainTopCocycle,ShiftedHom.mk₀_comp] using
    cochainResolutionExtClass_sourceIso
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (originalChainAsCochain C))
      (originalChainAsCochain ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C))
      (additiveFunctorOriginalChainCochainIso F C) r
      (originalChainAugmentationAsCochain ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C)
        (mappedOriginalChainAugmentation F C alpha))
      (originalChainTopShiftedCocycle ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) r
        (F.map a) (by change F.map (C.d _ _) ≫ F.map a = 0; rw [← F.map_comp,ha,F.map_zero]))

end LinearStudy