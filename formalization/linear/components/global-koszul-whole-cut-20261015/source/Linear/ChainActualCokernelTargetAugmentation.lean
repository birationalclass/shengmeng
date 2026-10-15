module
public import Linear.ChainActualCokernelAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {A : Type*} [Category* A] [Abelian A]

/-- The ACTUAL original quotient augmentation transported to a specified
actual target via a constructed cokernel iso. This defines a real chain
map;agreement with a separately defined geometric map is not assumed. -/
def originalChainCokernelTargetAugmentation (C : ChainComplex A ℕ)
    (T : A) (e : cokernel (C.d 1 0) ≅ T) : C ⟶ (ChainComplex.single₀ A).obj T :=
  originalChainCokernelAugmentation C ≫ (ChainComplex.single₀ A).map e.hom

/-- Its zero component is EXACTLY the ORIGINAL categorical quotient
projection followed by the SAME specified target identification. -/
theorem originalChainCokernelTargetAugmentation_f_zero (C : ChainComplex A ℕ)
    (T : A) (e : cokernel (C.d 1 0) ≅ T) :
    (originalChainCokernelTargetAugmentation C T e).f 0 = cokernel.π (C.d 1 0) ≫ e.hom := by
  simp only [originalChainCokernelTargetAugmentation,HomologicalComplex.comp_f,
    originalChainCokernelAugmentation_f_zero,ChainComplex.single₀_map_f_zero]
  rfl

/-- Reuse mathlib's native quasiIso_comp and quasiIso_of_isIso for this
SAME actual target augmentation. The original cokernel augmentation's
quasi-isomorphism is explicit here and derived in original applications. -/
theorem originalChainCokernelTargetAugmentation_quasiIso_of_cokernel
    (C : ChainComplex A ℕ) (T : A) (e : cokernel (C.d 1 0) ≅ T)
    (h : QuasiIso (originalChainCokernelAugmentation C)) :
    QuasiIso (originalChainCokernelTargetAugmentation C T e) := by
  letI := h
  unfold originalChainCokernelTargetAugmentation
  infer_instance

end LinearStudy