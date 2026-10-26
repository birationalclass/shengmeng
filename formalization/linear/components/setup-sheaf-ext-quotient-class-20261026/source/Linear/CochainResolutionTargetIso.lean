module
public import Linear.CochainResolutionExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe w d v u
variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasExt.{w} A] [HasDerivedCategory.{d} A]

/-- The SAME actual roof transforms contravariantly under an isomorphism
of its augmentation target. Only the original augmentation and the actual
isomorphism are inputs; no desired Ext-class equality is assumed. -/
theorem cochainResolutionExtClass_targetIso
    (K : CochainComplex A ℤ) {E Q M : A} (r : ℕ) (theta : E ≅ Q)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (beta : ShiftedHom K ((CochainComplex.singleFunctor A 0).obj M) (r:ℤ)) :
    (Ext.mk₀ theta.hom).comp
      (cochainResolutionExtClass K r
        (alpha ≫ (CochainComplex.singleFunctor A 0).map theta.hom) beta) (zero_add _) =
      cochainResolutionExtClass K r alpha beta := by
  apply Ext.ext
  simp only [Ext.comp_hom,Ext.mk₀_hom,cochainResolutionExtClass_hom,
    ShiftedHom.mk₀_comp,ShiftedHom.comp_mk₀,ShiftedHom.map,
    Functor.map_comp,IsIso.inv_comp,Category.assoc]
  rw [NatTrans.naturality_assoc]
  simp

end LinearStudy
