module
public import Linear.CochainResolutionTopSourceIso
public import Linear.ChainTopExtExactFunctorCompatibility
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
open CochainComplex.HomComplex
universe v u w d
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Converting the SAME original augmentation commutes with the ACTUAL
native chain-to-cochain extension of a source-complex isomorphism. -/
theorem originalChainAugmentationAsCochain_sourceIso
    (C D : ChainComplex A ℕ) (gamma : C ≅ D) {E : A}
    (alpha : D ⟶ (ChainComplex.single₀ A).obj E) :
    originalChainAugmentationAsCochain C (gamma.hom ≫ alpha) =
      ((ComplexShape.embeddingDownNat.extendFunctor A).mapIso gamma).hom ≫
        originalChainAugmentationAsCochain D alpha := by
  simp [originalChainAugmentationAsCochain,Functor.map_comp,Category.assoc]

/-- The SAME original ordered top functional commutes with the actual
source-complex isomorphism and native degree conversion. -/
theorem originalChainTopShiftedCocycle_sourceIso
    (C D : ChainComplex A ℕ) (gamma : C ≅ D) {M : A} (r : ℕ)
    (a : D.X r ⟶ M) (ha : D.d (r+1) r ≫ a = 0) :
    originalChainTopShiftedCocycle C r (gamma.hom.f r ≫ a)
        (by simp [← gamma.hom.comm_assoc,ha]) =
      (ShiftedHom.mk₀ _ rfl
        ((ComplexShape.embeddingDownNat.extendFunctor A).mapIso gamma).hom).comp
          (originalChainTopShiftedCocycle D r a ha) (add_zero _) := by
  simp only [ShiftedHom.mk₀_comp]
  dsimp only [originalChainTopShiftedCocycle,originalChainAsCochain]
  erw [← Cocycle.equivHomShift_symm_precomp,
    ← Cocycle.toSingleMk_precomp _ _ _ _ _
      ((ComplexShape.embeddingDownNat.extendFunctor A).mapIso gamma).hom]
  congr 2
  simp [ComplexShape.Embedding.extendFunctor_map,Functor.mapIso_hom,
    HomologicalComplex.extendMap_f gamma.hom ComplexShape.embeddingDownNat (show -(r:ℤ)=-(r:ℤ) from rfl),
    originalChainAsCochainXIso,Category.assoc]

variable [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- ACTUAL original chain-resolution Ext class is unchanged under a
constructed source-complex iso with the SAME augmentation and functional.
The desired class equality is not a premise. -/
theorem originalChainTopExtClass_sourceIso
    (C D : ChainComplex A ℕ) (gamma : C ≅ D) {E M : A} (r : ℕ)
    (alpha : D ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (a : D.X r ⟶ M) (ha : D.d (r+1) r ≫ a = 0) :
    originalChainTopExtClass C r (gamma.hom ≫ alpha) (gamma.hom.f r ≫ a)
      (by simp [← gamma.hom.comm_assoc,ha]) =
        originalChainTopExtClass D r alpha a ha := by
  letI := originalChainAugmentationAsCochain_quasiIso D alpha
  letI := originalChainAugmentationAsCochain_quasiIso C (gamma.hom ≫ alpha)
  rw [originalChainTopExtClass_eq_cochain,originalChainTopExtClass_eq_cochain]
  have h := cochainResolutionExtClass_sourceIso (originalChainAsCochain C) (originalChainAsCochain D)
    ((ComplexShape.embeddingDownNat.extendFunctor A).mapIso gamma) r
    (originalChainAugmentationAsCochain D alpha) (originalChainTopShiftedCocycle D r a ha)
  have hb := originalChainTopShiftedCocycle_sourceIso C D gamma r a ha
  simp only [ShiftedHom.mk₀_comp] at hb h
  simpa only [originalChainAugmentationAsCochain_sourceIso,hb] using h

end LinearStudy
