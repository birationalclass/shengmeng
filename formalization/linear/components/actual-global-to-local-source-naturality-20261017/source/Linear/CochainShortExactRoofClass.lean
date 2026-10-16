module
public import Linear.CochainResolutionExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- The SAME project roof constructor on the native short-exact mapping cone. -/
def cochainShortExactRoofClass (S : ShortComplex A) (hS : S.ShortExact) :
    Ext.{w} S.X₃ S.X₁ 1 := by
  let T := S.map (CochainComplex.singleFunctor A 0)
  letI := CochainComplex.mappingCone.quasiIso_descShortComplex
    (hS.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℤ) 0))
  exact cochainResolutionExtClass (CochainComplex.mappingCone T.f) 1
    (CochainComplex.mappingCone.descShortComplex T)
    (CochainComplex.mappingCone.triangle T.f).mor₃

/-- Calibrate the SAME roof against the native Ext class;no equality is a premise. -/
theorem cochainShortExactRoofClass_eq_extClass (S : ShortComplex A) (hS : S.ShortExact) :
    cochainShortExactRoofClass S hS = hS.extClass := by
  unfold cochainShortExactRoofClass
  apply Ext.ext
  rw [cochainResolutionExtClass_hom,ShortComplex.ShortExact.extClass_hom]
  simp only [ShiftedHom.mk₀_comp,ShiftedHom.comp_mk₀,ShiftedHom.map,
    DerivedCategory.singleFunctorIsoCompQ_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_inv_app,
    Category.id_comp]
  erw [CategoryTheory.Functor.map_id,Category.comp_id]
  rfl

/-- The native degree-zero CONTRAVARIANT boundary is MINUS the calibrated roof push.
This is a degree-one cone calibration,not yet the original Koszul epsilon/sign formula. -/
theorem cochainShortExactRoofClass_contravariant_zero_sign
    (S : ShortComplex A) (hS : S.ShortExact) {M : A} (a : S.X₁ ⟶ M) :
    Ext.δ hS 0 1 rfl (Ext.mk₀ a) =
      -(cochainShortExactRoofClass S hS).comp (Ext.mk₀ a) (add_zero 1) := by
  rw [cochainShortExactRoofClass_eq_extClass]
  simp [Ext.δ_apply,Units.smul_def]

end LinearStudy
