module
public import Linear.ChainResolutionTopExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The ACTUAL ordered top cocycle of the SAME original chain and functional. -/
def originalChainOrderedTopCocycle (C : ChainComplex A ℕ) {N : A} (r : ℕ)
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    Cocycle (originalChainAsCochain C) ((CochainComplex.singleFunctor A 0).obj N) (r : ℤ) :=
  Cocycle.toSingleMk ((originalChainAsCochainXIso C (-(r : ℤ)) r rfl).hom ≫ a)
    (by simp) (-(r : ℤ)-1) (by omega) (by
      rw [originalChainAsCochain_d C (-(r : ℤ)-1) (-(r : ℤ)) (r+1) r (by omega) rfl]
      simp only [Category.assoc,Iso.inv_hom_id_assoc,ha,comp_zero])

/-- The previously constructed ORIGINAL roof uses EXACTLY this ordered cocycle. -/
theorem originalChainTopExtClass_orderedCocycle [HasExt.{w} A] [HasDerivedCategory.{d} A]
    (C : ChainComplex A ℕ) {E N : A} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ A).obj E) [QuasiIso alpha]
    (a : C.X r ⟶ N) (ha : C.d (r+1) r ≫ a = 0) :
    letI := originalChainAugmentationAsCochain_quasiIso C alpha
    originalChainTopExtClass C r alpha a ha =
      cochainResolutionExtClass (originalChainAsCochain C) r
        (originalChainAugmentationAsCochain C alpha)
        (Cocycle.equivHomShift.symm (originalChainOrderedTopCocycle C r a ha)) := by
  letI := originalChainAugmentationAsCochain_quasiIso C alpha
  rfl

end LinearStudy
