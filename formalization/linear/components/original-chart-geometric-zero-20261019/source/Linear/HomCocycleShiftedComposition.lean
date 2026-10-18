module
public import Linear.CochainConeLiftClassAllDegrees
public import Mathlib.CategoryTheory.Shift.ShiftedHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The ACTUAL native cochain product induces the SAME shifted-Hom product.
This fixes the composition convention before arbitrary-degree Ext boundaries. -/
theorem actualHomCocycleComp_shiftedHom
    {F G K : CochainComplex A ℤ} {n m p : ℤ}
    (a : Cocycle F G n) (b : Cocycle G K m) (h : n+m=p) :
    Cocycle.equivHomShift.symm (actualHomCocycleComp a b h) =
      ShiftedHom.comp (Cocycle.equivHomShift.symm a) (Cocycle.equivHomShift.symm b) (by omega) := by
  ext i
  simp [actualHomCocycleComp,Cocycle.equivHomShift_symm_apply,ShiftedHom.comp,
    Cochain.rightShift,CochainComplex.shiftFunctor_map_f',
    CochainComplex.shiftFunctorAdd'_inv_app_f',Category.assoc]
  rw [Cochain.comp_v _ _ h i (i+n) (i+p) rfl (by omega),
    Cochain.v_comp_XIsoOfEq_hom]

end LinearStudy
