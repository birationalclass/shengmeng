module
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {A : Type*} [Category* A] [Abelian A]

/-- The ACTUAL canonical augmentation of an ORIGINAL nonnegative chain
complex to the actual categorical cokernel of its original d_1. This
constructs the actual map;identification with a geometric cut is separate. -/
def originalChainCokernelAugmentation (C : ChainComplex A ℕ) :
    C ⟶ (ChainComplex.single₀ A).obj (cokernel (C.d 1 0)) :=
  (ChainComplex.toSingle₀Equiv C _).symm ⟨cokernel.π (C.d 1 0),cokernel.condition _⟩

/-- Its degree-zero component is EXACTLY the original categorical
cokernel projection,not a freely chosen comparison morphism. -/
theorem originalChainCokernelAugmentation_f_zero (C : ChainComplex A ℕ) :
    (originalChainCokernelAugmentation C).f 0 = cokernel.π (C.d 1 0) := by
  simp [originalChainCokernelAugmentation]

/-- Actual positive exactness makes this SAME original cokernel
augmentation a quasi-isomorphism. This generic lemma assumes source
exactness explicitly;the original geometric application derives it. -/
theorem originalChainCokernelAugmentation_quasiIso (C : ChainComplex A ℕ)
    (he : ∀ p : ℕ,0 < p → C.ExactAt p) :
    QuasiIso (originalChainCokernelAugmentation C) := by
  refine ⟨fun p => ?_⟩
  cases p with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff]
    apply (ShortComplex.quasiIso_iff_of_zeros' _
      (by exact C.shape 0 0 (by simp)) (by rfl) (by rfl)).mpr
    constructor
    · change (ShortComplex.mk (C.d 1 0)
        ((originalChainCokernelAugmentation C).f 0) _).Exact
      simpa only [originalChainCokernelAugmentation_f_zero] using
        (ShortComplex.exact_of_g_is_cokernel
          (ShortComplex.mk (C.d 1 0) (cokernel.π (C.d 1 0)) (cokernel.condition _))
          (cokernelIsCokernel (C.d 1 0)))
    · change Epi ((originalChainCokernelAugmentation C).f 0)
      rw [originalChainCokernelAugmentation_f_zero]
      infer_instance
  | succ p =>
    rw [quasiIsoAt_iff_exactAt']
    · exact he (p+1) (by omega)
    · apply ChainComplex.exactAt_succ_single_obj

end LinearStudy