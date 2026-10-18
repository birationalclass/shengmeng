module
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- Native source Ext action on an ACTUAL integer-indexed injective cocycle. -/
theorem injectiveCochainCocycleClass_precompose {N P Q : A}
    (I : InjectiveResolution N) (q : ℕ) (g : P ⟶ Q)
    (c : Cocycle ((CochainComplex.singleFunctor A 0).obj Q) I.cochainComplex (q : ℤ)) :
    (Ext.mk₀ g).comp (I.extEquivCohomologyClass.symm (CohomologyClass.mk c)) (zero_add q) =
      I.extEquivCohomologyClass.symm (CohomologyClass.mk
        (c.precomp ((CochainComplex.singleFunctor A 0).map g))) := by
  letI := HasDerivedCategory.standard A
  apply Ext.ext
  simp only [Ext.comp_hom,Ext.mk₀_hom,I.extEquivCohomologyClass_symm_mk_hom,Category.assoc]
  rw [Cocycle.equivHomShift_symm_precomp,← ShiftedHom.mk₀_comp 0 rfl,
    ShiftedHom.map_comp,
    ShiftedHom.comp_assoc _ _ _ (add_zero _) (zero_add _) (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (add_zero _) (add_zero (q : ℤ)) (by simp)]
  simp

end LinearStudy
