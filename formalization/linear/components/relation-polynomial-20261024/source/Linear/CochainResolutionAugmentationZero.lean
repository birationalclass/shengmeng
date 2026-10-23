module
public import Linear.CochainResolutionExtSourceSquare
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- The actual roof of the zero cocycle is zero. -/
theorem cochainResolutionExtClass_zero
    (K : CochainComplex A ℤ) {E N : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha] :
    cochainResolutionExtClass K r alpha
      (0 : ShiftedHom K ((CochainComplex.singleFunctor A 0).obj N) (r : ℤ)) = 0 := by
  apply Ext.ext
  simp [cochainResolutionExtClass_hom,ShiftedHom.map]

omit [HasExt A] [HasDerivedCategory A] in
/-- Positive raw shifted morphisms between degree-zero single complexes
vanish degreewise. This is NOT a claim that their derived Ext vanishes. -/
theorem cochainSingle_positive_shiftedHom_zero {F N : A} (r : ℕ) (hr : 0 < r)
    (beta : ShiftedHom ((CochainComplex.singleFunctor A 0).obj F)
      ((CochainComplex.singleFunctor A 0).obj N) (r : ℤ)) : beta = 0 := by
  apply HomologicalComplex.from_single_hom_ext
  apply (show CategoryTheory.Limits.IsZero
    ((((CochainComplex.singleFunctor A 0).obj N)⟦(r : ℤ)⟧).X 0) from by
      simpa only [CochainComplex.shiftFunctor_obj_X',zero_add] using
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N
          (r : ℤ) (by omega)).eq_of_tgt

/-- An actual positive class represented on a bounded-above augmented
resolution pulls back to zero along its SAME degree-zero augmentation.
No projectivity, cohomology vanishing, or desired kernel identity is assumed. -/
theorem cochainResolutionExtClass_augmentation_precomp_zero
    (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] {E N : A}
    (r : ℕ) (hr : 0 < r)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (beta : ShiftedHom K ((CochainComplex.singleFunctor A 0).obj N) (r : ℤ)) :
    (Ext.mk₀ (alpha.f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).hom)).comp
      (cochainResolutionExtClass K r alpha beta) (zero_add r) = 0 := by
  let gamma : (CochainComplex.singleFunctor A 0).obj (K.X 0) ⟶ K :=
    HomologicalComplex.mkHomFromSingle (𝟙 (K.X 0)) (by
      rintro _ rfl
      apply (K.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt)
  let u := alpha.f 0 ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).hom
  have hsq : gamma ≫ alpha =
      (𝟙 _) ≫ (CochainComplex.singleFunctor A 0).map u := by
    apply HomologicalComplex.from_single_hom_ext
    simp [gamma,u,CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self]
  rw [cochainResolutionExtClass_sourceSquare K
    ((CochainComplex.singleFunctor A 0).obj (K.X 0)) r alpha (𝟙 _) gamma u hsq beta]
  have hb := cochainSingle_positive_shiftedHom_zero r hr
    ((ShiftedHom.mk₀ 0 rfl gamma).comp beta (add_zero _))
  rw [hb,cochainResolutionExtClass_zero]
end LinearStudy
