module
public import Linear.HomCocycleShiftedComposition
public import Linear.CochainConeLiftDerivedBridge
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v d
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]

/-- EVERY-degree cone class equality induces the SAME ACTUAL derived
shifted-Hom product with the exact native (-1)^q sign. -/
theorem cochainConeLiftDerived_allDegrees
    (S : ShortComplex (CochainComplex A ℤ)) (K : CochainComplex A ℤ) (q : ℤ)
    (a : Cocycle S.X₁ K q) (b : Cochain S.X₂ K q) (c : Cocycle S.X₃ K (q+1))
    (hb : (Cochain.ofHom S.f).comp b (zero_add q) = a.val)
    (hc : δ q (q+1) b = (Cochain.ofHom S.g).comp c.val (zero_add (q+1))) :
    ShiftedHom.map (Cocycle.equivHomShift.symm
      (c.precomp (CochainComplex.mappingCone.descShortComplex S))) DerivedCategory.Q =
      ShiftedHom.map (q.negOnePow • ShiftedHom.comp
        (Cocycle.equivHomShift.symm (CochainComplex.mappingCone.fst S.f))
        (Cocycle.equivHomShift.symm a) (show q+1=q+1 by rfl)) DerivedCategory.Q := by
  have h := cochainDerivedMap_eq_of_classEq _ _
    (cochainConeLiftClass_allDegrees S K q a b c hb hc)
  simpa only [Units.smul_def,map_zsmul,actualHomCocycleComp_shiftedHom] using h

/-- Replacing fst by the SAME native triangle third map changes the factor
to (-1)^(q+1),the factor in the native contravariant Ext boundary. -/
theorem cochainConeLiftTriangle_allDegrees
    (S : ShortComplex (CochainComplex A ℤ)) (K : CochainComplex A ℤ) (q : ℤ)
    (a : Cocycle S.X₁ K q) (b : Cochain S.X₂ K q) (c : Cocycle S.X₃ K (q+1))
    (hb : (Cochain.ofHom S.f).comp b (zero_add q) = a.val)
    (hc : δ q (q+1) b = (Cochain.ofHom S.g).comp c.val (zero_add (q+1))) :
    ShiftedHom.map (Cocycle.equivHomShift.symm
      (c.precomp (CochainComplex.mappingCone.descShortComplex S))) DerivedCategory.Q =
      ShiftedHom.map ((q+1).negOnePow • ShiftedHom.comp
        (CochainComplex.mappingCone.triangle S.f).mor₃
        (Cocycle.equivHomShift.symm a) (show q+1=q+1 by rfl)) DerivedCategory.Q := by
  rw [cochainConeTriangle_mor3_neg_fst,map_neg,ShiftedHom.neg_comp,
    Int.negOnePow_succ,Units.neg_smul,smul_neg,neg_neg]
  exact cochainConeLiftDerived_allDegrees S K q a b c hb hc

end LinearStudy
