module
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.CategoryTheory.Shift.ShiftedHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
open CochainComplex.HomComplex
universe u v
variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- The ACTUAL degree-zero cocycle uses the native shifted-Hom unit. -/
theorem cochainCocycleOfHom_shifted {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    Cocycle.equivHomShift.symm (Cocycle.ofHom f) = ShiftedHom.mk₀ 0 rfl f := by
  ext p
  simp [Cocycle.equivHomShift_symm_apply,ShiftedHom.mk₀,Cochain.rightShift_v,CategoryTheory.shiftFunctorZero',
    CochainComplex.shiftFunctorZero_inv_app_f,HomologicalComplex.XIsoOfEq]

end LinearStudy
