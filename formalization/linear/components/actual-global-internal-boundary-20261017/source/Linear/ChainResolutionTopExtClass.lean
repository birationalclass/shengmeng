module
public import Linear.ChainResolutionAsCochain
public import Linear.CochainResolutionTopExtNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe w w' v u
variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasExt.{w} A] [HasDerivedCategory.{w'} A]

/-- Construct the actual derived Ext class from the SAME original chain
resolution,actual augmentation and original top functional. Preserve the
actual degrees/differentials through the native n↦-n embedding. No global
projectivity or freely supplied class/representative identity is assumed. -/
def originalChainTopExtClass (C : ChainComplex A ℕ) {E M : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (f : C.X r ⟶ M) (hf : C.d (r+1) r ≫ f = 0) : Ext.{w} E M r := by
  letI := originalChainAugmentationAsCochain_quasiIso C alpha
  refine cochainResolutionTopExtClass (originalChainAsCochain C) r
    (originalChainAugmentationAsCochain C alpha)
    ((originalChainAsCochainXIso C (-(r : ℤ)) r rfl).hom ≫ f) ?_
  rw [originalChainAsCochain_d C (-(r : ℤ)-1) (-(r : ℤ)) (r+1) r (by omega) rfl]
  simp only [Category.assoc,Iso.inv_hom_id_assoc,hf,comp_zero]

/-- Coefficient pushforward of the actual class uses the SAME original
functional f followed by g. This is a derived-category identity,not an
affine module-Ext replacement for the original sheaf argument. -/
theorem originalChainTopExtClass_comp_mk₀ (C : ChainComplex A ℕ) {E M N : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (f : C.X r ⟶ M) (hf : C.d (r+1) r ≫ f = 0) (g : M ⟶ N) :
    (originalChainTopExtClass C r alpha f hf).comp (Ext.mk₀ g) (add_zero _) =
      originalChainTopExtClass C r alpha (f ≫ g) (by simp [reassoc_of% hf]) := by
  letI := originalChainAugmentationAsCochain_quasiIso C alpha
  simpa only [originalChainTopExtClass,Category.assoc] using
    cochainResolutionTopExtClass_comp_mk₀ (originalChainAsCochain C) r
      (originalChainAugmentationAsCochain C alpha)
      ((originalChainAsCochainXIso C (-(r : ℤ)) r rfl).hom ≫ f)
      (by
        rw [originalChainAsCochain_d C (-(r : ℤ)-1) (-(r : ℤ)) (r+1) r (by omega) rfl]
        simp only [Category.assoc,Iso.inv_hom_id_assoc,hf,comp_zero]) g

end LinearStudy
