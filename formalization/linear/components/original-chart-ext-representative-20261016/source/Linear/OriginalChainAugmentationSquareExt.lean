module
public import Linear.OriginalChainTopExtTargetIso
public import Linear.OriginalChainTopExtSourceIso
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe v u w d
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A proved WHOLE augmentation square and actual source/target isos
transfer the original augmentation's quasi-isomorphism. The second
augmentation's exactness is DERIVED,not an additional premise. -/
theorem originalChainAugmentationSquare_quasiIso
    (C D : ChainComplex A ℕ) (gamma : C ≅ D) {E Q : A} (theta : E ≅ Q)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (beta : D ⟶ (ChainComplex.single₀ A).obj Q)
    (square : alpha ≫ (ChainComplex.single₀ A).map theta.hom = gamma.hom ≫ beta) :
    QuasiIso beta := by
  haveI : QuasiIso (gamma.hom ≫ beta) := by rw [← square];infer_instance
  exact quasiIso_of_comp_left gamma.hom beta

variable [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- COMBINE the actual target-iso action with source-iso invariance.
The only square input is equality of actual chain maps,which the original
chart construction proves independently. No Ext equality is a premise;
the SAME top functional and native degree-zero Ext action are retained. -/
theorem originalChainTopExtClass_augmentationSquare
    (C D : ChainComplex A ℕ) (gamma : C ≅ D) {E Q M : A}
    (r : ℕ) (theta : E ≅ Q)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (beta : D ⟶ (ChainComplex.single₀ A).obj Q)
    (square : alpha ≫ (ChainComplex.single₀ A).map theta.hom = gamma.hom ≫ beta)
    (a : D.X r ⟶ M) (ha : D.d (r+1) r ≫ a = 0) :
    letI := originalChainAugmentationSquare_quasiIso C D gamma theta alpha beta square
    (Ext.mk₀ theta.hom).comp (originalChainTopExtClass D r beta a ha) (zero_add _) =
      originalChainTopExtClass C r alpha (gamma.hom.f r ≫ a)
        (by simp [← gamma.hom.comm_assoc,ha]) := by
  letI := originalChainAugmentationSquare_quasiIso C D gamma theta alpha beta square
  have h := originalChainTopExtClass_targetIso C r theta alpha (gamma.hom.f r ≫ a)
    (by simp [← gamma.hom.comm_assoc,ha])
  have hc := originalChainTopExtClass_sourceIso C D gamma r beta a ha
  have ht : originalChainTopExtClass C r
      (alpha ≫ (ChainComplex.single₀ A).map theta.hom) (gamma.hom.f r ≫ a)
        (by simp [← gamma.hom.comm_assoc,ha]) =
      originalChainTopExtClass C r (gamma.hom ≫ beta) (gamma.hom.f r ≫ a)
        (by simp [← gamma.hom.comm_assoc,ha]) := by
    congr 1
  rw [ht,hc] at h
  exact h

end LinearStudy
