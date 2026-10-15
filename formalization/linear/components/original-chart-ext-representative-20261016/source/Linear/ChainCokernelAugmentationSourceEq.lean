module
public import Linear.ChainActualCokernelTargetAugmentation
public import Linear.OriginalChainTopExtSourceIso
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe v u w d
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Transport the SAME original quotient augmentation only through a
PROVED equality of actual source complexes and its induced cokernel iso. -/
theorem originalChainCokernelTargetAugmentation_sourceEq
    (C D : ChainComplex A ℕ) (h : C = D) (T : A) (e : cokernel (D.d 1 0) ≅ T) :
    originalChainCokernelTargetAugmentation C T
      (eqToIso (congrArg (fun K : ChainComplex A ℕ => cokernel (K.d 1 0)) h) ≪≫ e) =
      (eqToIso h).hom ≫ originalChainCokernelTargetAugmentation D T e := by
  cases h
  simp

/-- The original augmentation's quasiiso transfers through the PROVED
source equality;the actual original application supplies that equality. -/
theorem originalChainCokernelTargetAugmentation_quasiIso_sourceEq
    (C D : ChainComplex A ℕ) (h : C = D) (T : A) (e : cokernel (D.d 1 0) ≅ T)
    (he : QuasiIso (originalChainCokernelTargetAugmentation D T e)) :
    QuasiIso (originalChainCokernelTargetAugmentation C T
      (eqToIso (congrArg (fun K : ChainComplex A ℕ => cokernel (K.d 1 0)) h) ≪≫ e)) := by
  cases h
  simpa using he

variable [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- The actual roof and SAME top functional agree after the original
source equality. No independent class/representative identity is supplied. -/
theorem originalChainTopExtClass_cokernelSourceEq
    (C D : ChainComplex A ℕ) (h : C = D) (T : A) (e : cokernel (D.d 1 0) ≅ T)
    [he : QuasiIso (originalChainCokernelTargetAugmentation D T e)]
    {M : A} (r : ℕ) (a : D.X r ⟶ M) (ha : D.d (r+1) r ≫ a = 0) :
    letI := originalChainCokernelTargetAugmentation_quasiIso_sourceEq C D h T e he
    originalChainTopExtClass C r
      (originalChainCokernelTargetAugmentation C T
        (eqToIso (congrArg (fun K : ChainComplex A ℕ => cokernel (K.d 1 0)) h) ≪≫ e))
      ((eqToIso h).hom.f r ≫ a) (by cases h;simpa using ha) =
        originalChainTopExtClass D r (originalChainCokernelTargetAugmentation D T e) a ha := by
  cases h
  simp

end LinearStudy
