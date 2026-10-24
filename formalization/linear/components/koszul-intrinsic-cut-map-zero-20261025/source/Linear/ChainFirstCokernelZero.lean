module
public import Linear.ChainActualCokernelAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {A : Type*} [Category* A] [Abelian A]

/-- For the SAME nonnegative chain complex, exactness at zero makes
its ORIGINAL d1 an epimorphism. Exactness is an explicit generic premise. -/
theorem originalChainFirstDifferential_epi_of_exactAt_zero
    (C : ChainComplex A ℕ) (he : C.ExactAt 0) : Epi (C.d 1 0) := by
  have he' : (C.sc' 1 0 0).Exact :=
    (C.exactAt_iff' 1 0 0 (by simp) (by simp)).mp he
  exact ((C.sc' 1 0 0).exact_iff_epi (C.shape 0 0 (by simp))).mp he'

/-- The ACTUAL cokernel of the original d1 vanishes when the SAME
original complex is exact at zero. No chosen zero-object comparison is assumed. -/
theorem originalChainFirstCokernel_isZero_of_exactAt_zero
    (C : ChainComplex A ℕ) (he : C.ExactAt 0) : IsZero (cokernel (C.d 1 0)) := by
  let := originalChainFirstDifferential_epi_of_exactAt_zero C he
  exact isZero_cokernel_of_epi (C.d 1 0)

end LinearStudy
