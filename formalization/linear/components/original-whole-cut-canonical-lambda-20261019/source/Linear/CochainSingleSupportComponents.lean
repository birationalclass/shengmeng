module
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Abelian.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A SAME augmentation into E[0] has zero pullback component off degree0. -/
theorem cochainSingleAugmentation_precomp_v_zero
    {K L : CochainComplex A ℤ} {E : A} (q j l : ℤ) (hjl : j+q=l)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E)
    (c : Cocycle ((CochainComplex.singleFunctor A 0).obj E) L q) (hj : j ≠ 0) :
    (c.precomp alpha).val.v j l hjl = 0 := by
  change ((Cochain.ofHom alpha).comp c.val (zero_add q)).v j l hjl = 0
  rw [Cochain.zero_cochain_comp_v,Cochain.ofHom_v]
  have hz : IsZero (((CochainComplex.singleFunctor A 0).obj E).X j) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 E j hj
  rw [hz.eq_of_tgt (alpha.f j) 0,zero_comp]

/-- The ACTUAL top-functional cochain followed by a resolution augmentation
has no component off the SAME original top source degree. -/
theorem cochainTopFunctional_postcomp_v_zero
    {K L : CochainComplex A ℤ} {N : A} (q j l : ℤ) (hjl : j+q=l)
    (a : K.X (-q) ⟶ N) (phi : (CochainComplex.singleFunctor A 0).obj N ⟶ L)
    (hj : j ≠ -q) :
    ((Cochain.toSingleMk a (show -q+q=0 by omega)).comp (Cochain.ofHom phi)
      (add_zero q)).v j l hjl = 0 := by
  rw [Cochain.comp_zero_cochain_v,Cochain.toSingleMk_v_eq_zero a _ j l hjl hj,
    zero_comp]

end LinearStudy
